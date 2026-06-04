use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
    sync::{mpsc, Arc, Condvar, Mutex},
    time::{Duration, Instant},
};

use bitcoin::{
    hashes::Hash,
    p2p::{
        address::AddrV2Message,
        message::NetworkMessage,
        message_blockdata::{GetBlocksMessage, GetHeadersMessage, Inventory},
        ServiceFlags,
    },
};
use bitcoin::{BlockHash, Network};
use bitcoinkernel::{
    core::BlockHashExt, BlockTreeEntry, ChainstateManager, Context, ProcessBlockHeaderResult,
};
use log::{debug, info, warn};
use p2p::{
    handshake::{ConnectionConfig, ProtocolVersion},
    net::{ConnectionReader, ConnectionWriter, READ_TIMEOUT},
};

use crate::{
    ext::{CrateBlockExt, CrateHeaderExt},
    logging::Category,
    peer_manager::{self, Destination},
    socks5::Socks5Proxy,
};

const PROTOCOL_VERSION: ProtocolVersion = 70015;
const MAX_LOCATOR_HASHES: usize = 101;
const DOWNLOAD_BATCH_SIZE: usize = 16;
const PEER_STALL_TIMEOUT: Duration = Duration::from_secs(30);

#[derive(Default)]
pub struct DownloadState {
    queue: VecDeque<BlockHash>,
    in_flight: HashSet<BlockHash>,
    buffer: HashMap<BlockHash /* prev */, bitcoinkernel::Block>,
}

impl DownloadState {
    fn pop_batch(&mut self, batch_size: usize) -> Vec<BlockHash> {
        let mut batch = Vec::with_capacity(batch_size);
        while batch.len() < batch_size {
            let Some(hash) = self.queue.pop_front() else {
                break;
            };
            if self.in_flight.insert(hash) {
                batch.push(hash);
            }
        }
        batch
    }

    fn claim(&mut self, hashes: Vec<BlockHash>) -> Vec<BlockHash> {
        hashes
            .into_iter()
            .filter(|hash| self.in_flight.insert(*hash))
            .collect()
    }

    fn release(&mut self, hash: &BlockHash) -> bool {
        self.in_flight.remove(hash)
    }

    fn requeue_unreceived(&mut self, inventory: &HashSet<BlockHash>) {
        if inventory.is_empty() {
            return;
        }
        for hash in inventory {
            self.in_flight.remove(hash);
            self.queue.push_front(*hash);
        }
        debug!(target: Category::NET, "Re-enqueued {} unreceived blocks", inventory.len());
    }

    fn buffer_block(&mut self, prev_blockhash: BlockHash, block: bitcoinkernel::Block) {
        self.buffer.insert(prev_blockhash, block);
    }

    /// `is_connected` is a parameter so the buffer can be tested without a
    /// chainstate. What remains once the peers go idle is a competing branch,
    /// whose parents stay off the active chain until the kernel has enough of
    /// the branch to adopt it.
    fn take_connectable(
        &mut self,
        is_connected: impl Fn(&BlockHash) -> bool,
    ) -> Option<bitcoinkernel::Block> {
        if let Some(prev) = self.buffer.keys().copied().find(&is_connected) {
            return self.buffer.remove(&prev);
        }
        if !self.queue.is_empty() || !self.in_flight.is_empty() {
            return None;
        }
        let prev = self.buffer_head()?;
        self.buffer.remove(&prev)
    }

    fn buffered_hashes(&self) -> HashSet<BlockHash> {
        self.buffer
            .values()
            .map(|block| BlockHash::from_byte_array(block.hash().into()))
            .collect()
    }

    fn buffer_head(&self) -> Option<BlockHash> {
        let buffered = self.buffered_hashes();
        self.buffer
            .keys()
            .copied()
            .find(|prev| !buffered.contains(prev))
    }
}

pub struct NodeState {
    pub addr_tx: mpsc::Sender<Vec<AddrV2Message>>,
    pub context: Arc<Context>,
    pub chainman: Arc<ChainstateManager>,
    pub download: Mutex<DownloadState>,
    pub connectable: Condvar,
}

impl NodeState {
    pub fn is_on_active_chain(&self, block_hash: &bitcoin::BlockHash) -> bool {
        let hash = bitcoinkernel::BlockHash::from(block_hash.to_byte_array());
        match self.chainman.get_block_tree_entry(&hash) {
            Some(entry) => self.chainman.active_chain().contains(&entry),
            None => false,
        }
    }

    pub fn buffer_block(&self, prev_blockhash: bitcoin::BlockHash, block: bitcoinkernel::Block) {
        self.download
            .lock()
            .unwrap()
            .buffer_block(prev_blockhash, block);
        self.connectable.notify_one();
    }

    /// Times out so the caller can re-check its shutdown flag.
    pub fn wait_for_connectable(&self, timeout: Duration) -> Option<bitcoinkernel::Block> {
        let mut state = self.download.lock().unwrap();
        if let Some(block) = self.take_connectable(&mut state) {
            return Some(block);
        }
        let (mut state, _) = self.connectable.wait_timeout(state, timeout).unwrap();
        self.take_connectable(&mut state)
    }

    fn take_connectable(&self, state: &mut DownloadState) -> Option<bitcoinkernel::Block> {
        state.take_connectable(|prev| self.is_on_active_chain(prev))
    }
}

/// State Machine for setting up a connection and getting blocks from a peer
///
/// ```text
///                       [*]
///                        │
///                        ▼
///              ┌─────────────────┐   got 2000 headers:
///         ┌───▶│ AwaitingHeaders │──┐  ask for the next batch
///         │    └─────────────────┘◀─┘
///         │                 │
///         │                 │ header sync done: build the queue,
///         │                 │ then take the first batch
///         │                 ▼
///         │    ┌─────────────────┐   block arrives (batch not done), or
///         │    │  AwaitingBlock  │──┐  batch done + queue has more:
///         │    └─────────────────┘◀─┘  take the next batch
///         │       ▲         │
///         │  inv/ │         │ batch done AND queue empty
///         │  hdrs │         ▼
///         │    ┌─────────────────┐   nothing to claim: ask again
///         └────│   AwaitingInv   │──┐
///              └─────────────────┘◀─┘
/// ```
///
/// The left edge (AwaitingInv ─▶ AwaitingHeaders) is the unconnecting-headers
/// path: a peer's announced headers don't connect, so we resync headers.
#[derive(Default)]
pub enum PeerStateMachine {
    #[default]
    AwaitingHeaders,
    AwaitingInv,
    AwaitingBlock(AwaitingBlock),
}

pub struct AwaitingBlock {
    pub peer_inventory: HashSet<bitcoin::BlockHash>,
}

fn build_block_locators(tip: BlockTreeEntry<'_>) -> Vec<BlockHash> {
    let height = tip.height();
    assert!(height >= 0);
    let mut locators = Vec::with_capacity(MAX_LOCATOR_HASHES);
    let mut current_height = height;
    let mut step = 1;
    loop {
        let entry = tip
            .ancestor(current_height)
            .expect("height is between zero and the tip height");
        let hash = BlockHash::from_byte_array(entry.block_hash().to_bytes());
        locators.push(hash);
        if current_height == 0 || locators.len() >= MAX_LOCATOR_HASHES {
            break;
        }
        current_height = (current_height - step).max(0);
        if locators.len() > 10 {
            step *= 2;
        }
    }
    locators
}

fn populate_download_queue(chainman: &ChainstateManager, download: &Mutex<DownloadState>) {
    if !download.lock().unwrap().queue.is_empty() {
        return;
    }
    let active = chainman.active_chain();
    let best = match chainman.best_entry() {
        Some(entry) => entry,
        None => return,
    };
    let best_height = best.height();
    let mut hashes = Vec::new();
    let mut current = best;
    let fork_point = loop {
        if active.contains(&current) {
            break BlockHash::from_byte_array(current.block_hash().to_bytes());
        }
        hashes.push(BlockHash::from_byte_array(current.block_hash().to_bytes()));
        match current.prev() {
            Some(prev) => current = prev,
            None => return,
        }
    };
    if hashes.is_empty() {
        return;
    }
    let fork_height = best_height - hashes.len() as i32;
    hashes.reverse();
    let mut state = download.lock().unwrap();
    if !state.queue.is_empty() {
        return;
    }
    // Re-queueing held blocks would never let the peers go idle.
    let buffered = state.buffered_hashes();
    let queued: VecDeque<BlockHash> = hashes
        .into_iter()
        .filter(|hash| !buffered.contains(hash) && !state.in_flight.contains(hash))
        .collect();
    if queued.is_empty() {
        return;
    }
    info!(
        target: Category::NET,
        "Built download queue with {} blocks (heights {} to {}) forking at {}",
        queued.len(),
        fork_height + 1,
        best_height,
        fork_point
    );
    state.queue = queued;
}

fn create_getheaders_message(locator_hashes: Vec<bitcoin::BlockHash>) -> NetworkMessage {
    NetworkMessage::GetHeaders(GetHeadersMessage {
        version: PROTOCOL_VERSION,
        locator_hashes,
        stop_hash: bitcoin::BlockHash::all_zeros(),
    })
}

fn create_getblocks_message(locator_hashes: Vec<bitcoin::BlockHash>) -> NetworkMessage {
    NetworkMessage::GetBlocks(GetBlocksMessage {
        version: PROTOCOL_VERSION,
        locator_hashes,
        stop_hash: bitcoin::BlockHash::all_zeros(),
    })
}

fn create_getdata_message(block_hashes: &[bitcoin::BlockHash]) -> NetworkMessage {
    let inventory: Vec<Inventory> = block_hashes
        .iter()
        .map(|hash| Inventory::WitnessBlock(*hash))
        .collect();

    NetworkMessage::GetData(inventory)
}

pub fn process_message(
    state_machine: PeerStateMachine,
    event: NetworkMessage,
    node_state: &NodeState,
) -> (PeerStateMachine, Vec<NetworkMessage>) {
    // Always process the ping first as a special case.
    if let NetworkMessage::Ping(nonce) = event {
        info!(target: Category::NET, "Received ping, responding pong.");
        return (state_machine, vec![NetworkMessage::Pong(nonce)]);
    }

    if let NetworkMessage::AddrV2(payload) = event {
        info!(target: Category::NET, "Received {} net addresses", payload.len());
        // If the address manager has a full queue these net addresses should be dropped.
        let _ = node_state.addr_tx.send(payload);
        return (state_machine, vec![]);
    }

    match state_machine {
        PeerStateMachine::AwaitingHeaders => match event {
            NetworkMessage::Headers(headers) => {
                let msg_len = headers.len();
                for header in headers.into_iter() {
                    let result = node_state.chainman.process_block_header(&header.convert());
                    match result {
                        Ok(ProcessBlockHeaderResult::Valid) => {
                            debug!(target: Category::KERNEL, "Processed header: {}", header.time);
                            continue;
                        }
                        _ => {
                            warn!(target: Category::KERNEL, "Rejected header {}", header.block_hash());
                            break;
                        }
                    }
                }

                if msg_len != 2000 {
                    populate_download_queue(&node_state.chainman, &node_state.download);
                    let batch = node_state
                        .download
                        .lock()
                        .unwrap()
                        .pop_batch(DOWNLOAD_BATCH_SIZE);
                    if !batch.is_empty() {
                        return (
                            PeerStateMachine::AwaitingBlock(AwaitingBlock {
                                peer_inventory: batch.iter().cloned().collect(),
                            }),
                            vec![create_getdata_message(&batch)],
                        );
                    }
                    let locators = build_block_locators(node_state.chainman.active_chain().tip());
                    return (
                        PeerStateMachine::AwaitingInv,
                        vec![create_getblocks_message(locators)],
                    );
                }

                let locators = build_block_locators(node_state.chainman.best_entry().unwrap());
                (
                    PeerStateMachine::AwaitingHeaders,
                    vec![create_getheaders_message(locators)],
                )
            }
            message => {
                debug!(target: Category::NET, "Ignoring message: {:?}", message);
                (PeerStateMachine::AwaitingHeaders, vec![])
            }
        },
        PeerStateMachine::AwaitingInv => match event {
            NetworkMessage::Headers(headers) => {
                let mut announced = Vec::with_capacity(headers.len());
                for header in headers {
                    let block_hash = header.block_hash();
                    let valid = matches!(
                        node_state.chainman.process_block_header(&header.convert()),
                        Ok(ProcessBlockHeaderResult::Valid)
                    );
                    if !valid {
                        warn!(target: Category::KERNEL, "Rejected announced header {}", block_hash);
                        break;
                    }
                    announced.push(block_hash);
                }

                if announced.is_empty() {
                    let locators = build_block_locators(node_state.chainman.best_entry().unwrap());
                    return (
                        PeerStateMachine::AwaitingHeaders,
                        vec![create_getheaders_message(locators)],
                    );
                }

                let claimed = node_state.download.lock().unwrap().claim(announced);
                if claimed.is_empty() {
                    return (PeerStateMachine::AwaitingInv, vec![]);
                }
                debug!(target: Category::NET, "Requesting {} announced blocks", claimed.len());
                (
                    PeerStateMachine::AwaitingBlock(AwaitingBlock {
                        peer_inventory: claimed.iter().copied().collect(),
                    }),
                    vec![create_getdata_message(&claimed)],
                )
            }
            NetworkMessage::Inv(inventory) => {
                debug!(target: Category::NET, "Received inventory with {} items", inventory.len());
                let block_hashes: Vec<bitcoin::BlockHash> = inventory
                    .iter()
                    .filter_map(|inv| match inv {
                        Inventory::Block(hash) => Some(*hash),
                        _ => None,
                    })
                    .collect();

                if !block_hashes.is_empty() {
                    // The queue walks block tree entries, which need these
                    // headers first.
                    let locators = build_block_locators(node_state.chainman.best_entry().unwrap());
                    (
                        PeerStateMachine::AwaitingHeaders,
                        vec![create_getheaders_message(locators)],
                    )
                } else {
                    (PeerStateMachine::AwaitingInv, vec![])
                }
            }
            message => {
                debug!(target: Category::NET, "Ignoring message: {:?}", message);
                (PeerStateMachine::AwaitingInv, vec![])
            }
        },
        PeerStateMachine::AwaitingBlock(mut block_state) => match event {
            NetworkMessage::Block(block) => {
                let block_hash = block.block_hash();
                let prev_blockhash = block.header.prev_blockhash;
                block_state.peer_inventory.remove(&block_hash);
                // Another peer may have delivered it already.
                if node_state.download.lock().unwrap().release(&block_hash) {
                    node_state.buffer_block(prev_blockhash, block.convert());
                }

                if block_state.peer_inventory.is_empty() {
                    let batch = node_state
                        .download
                        .lock()
                        .unwrap()
                        .pop_batch(DOWNLOAD_BATCH_SIZE);
                    if !batch.is_empty() {
                        (
                            PeerStateMachine::AwaitingBlock(AwaitingBlock {
                                peer_inventory: batch.iter().cloned().collect(),
                            }),
                            vec![create_getdata_message(&batch)],
                        )
                    } else {
                        let locators =
                            build_block_locators(node_state.chainman.active_chain().tip());
                        (
                            PeerStateMachine::AwaitingInv,
                            vec![create_getblocks_message(locators)],
                        )
                    }
                } else {
                    (PeerStateMachine::AwaitingBlock(block_state), vec![])
                }
            }
            message => {
                debug!(target: Category::NET, "Ignoring message: {:?}", message);
                (PeerStateMachine::AwaitingBlock(block_state), vec![])
            }
        },
    }
}

fn stalled(state: &PeerStateMachine, last_progress: Instant) -> bool {
    !matches!(state, PeerStateMachine::AwaitingInv) && last_progress.elapsed() > PEER_STALL_TIMEOUT
}

fn delivers_requested_block(state: &PeerStateMachine, msg: &NetworkMessage) -> bool {
    matches!(
        (state, msg),
        (PeerStateMachine::AwaitingBlock(awaiting), NetworkMessage::Block(block))
            if awaiting.peer_inventory.contains(&block.block_hash())
    )
}

pub struct BitcoinPeer {
    dest: Destination,
    writer: Arc<ConnectionWriter>,
    reader: ConnectionReader,
    state_machine: PeerStateMachine,
    last_progress: Instant,
}

impl fmt::Display for BitcoinPeer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.dest)
    }
}

impl BitcoinPeer {
    pub fn new(
        destination: Destination,
        proxy: Option<Socks5Proxy>,
        network: Network,
        node_state: &NodeState,
    ) -> Result<Self, p2p::net::Error> {
        let height = node_state.chainman.active_chain().height();
        let conf = ConnectionConfig::new()
            .change_network(network)
            .our_height(height)
            .request_addr()
            .set_service_requirement(ServiceFlags::NETWORK)
            .offer_services(ServiceFlags::WITNESS)
            .user_agent("/kernel-node:0.1.0/".into());
        let (writer, reader) =
            peer_manager::connect(conf, &destination, proxy.as_ref(), READ_TIMEOUT)?;

        let locators = build_block_locators(node_state.chainman.best_entry().unwrap());
        debug!(target: Category::NET, "Sending headers message...");
        writer.send_message(create_getheaders_message(locators))?;
        let peer = BitcoinPeer {
            dest: destination,
            writer: Arc::new(writer),
            reader,
            state_machine: PeerStateMachine::AwaitingHeaders,
            last_progress: Instant::now(),
        };
        Ok(peer)
    }

    pub fn writer(&self) -> Arc<ConnectionWriter> {
        Arc::clone(&self.writer)
    }

    pub fn is_stalled(&self) -> bool {
        stalled(&self.state_machine, self.last_progress)
    }

    pub fn release_in_flight(&self, download: &Mutex<DownloadState>) {
        if let PeerStateMachine::AwaitingBlock(state) = &self.state_machine {
            download
                .lock()
                .unwrap()
                .requeue_unreceived(&state.peer_inventory);
        }
    }

    fn receive_message(&mut self) -> Result<NetworkMessage, p2p::net::Error> {
        Ok(self
            .reader
            .read_message()?
            .expect("v1 only supported currently"))
    }

    pub fn receive_and_process_message(
        &mut self,
        node_state: &NodeState,
    ) -> Result<(), p2p::net::Error> {
        let msg = self.receive_message()?;
        let delivered = delivers_requested_block(&self.state_machine, &msg);
        let old_state = std::mem::take(&mut self.state_machine);
        let (peer_state_machine, mut messages) = process_message(old_state, msg, node_state);
        self.state_machine = peer_state_machine;
        let requested = messages.iter().any(|message| {
            matches!(
                message,
                NetworkMessage::GetHeaders(_) | NetworkMessage::GetData(_)
            )
        });
        if delivered || requested {
            self.last_progress = Instant::now();
        }
        for message in messages.drain(..) {
            self.writer.send_message(message)?
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn hash(n: u8) -> BlockHash {
        BlockHash::from_byte_array([n; 32])
    }

    fn download(queue: &[BlockHash], in_flight: &[BlockHash]) -> DownloadState {
        DownloadState {
            queue: queue.iter().copied().collect(),
            in_flight: in_flight.iter().copied().collect(),
            ..Default::default()
        }
    }

    fn block_chain(len: usize) -> Vec<bitcoin::Block> {
        let mut blocks = Vec::with_capacity(len);
        let mut prev = bitcoin::blockdata::constants::genesis_block(Network::Regtest).block_hash();
        for i in 0..len {
            let mut block = bitcoin::blockdata::constants::genesis_block(Network::Regtest);
            block.header.prev_blockhash = prev;
            block.header.nonce = i as u32;
            prev = block.block_hash();
            blocks.push(block);
        }
        blocks
    }

    #[test]
    fn pop_batch_returns_requested_count() {
        let mut d = download(&[hash(1), hash(2), hash(3), hash(4)], &[]);
        assert_eq!(d.pop_batch(2), vec![hash(1), hash(2)]);
        assert_eq!(d.queue.len(), 2);
    }

    #[test]
    fn release_reports_in_flight_membership() {
        let mut d = download(&[hash(1)], &[]);
        assert!(!d.release(&hash(1)));
        d.pop_batch(1);
        assert!(d.release(&hash(1)));
        assert!(!d.release(&hash(1)));
        assert!(!d.release(&hash(2)));
    }

    #[test]
    fn pop_batch_marks_in_flight() {
        let mut d = download(&[hash(1), hash(2)], &[]);
        d.pop_batch(2);
        assert!(d.in_flight.contains(&hash(1)));
        assert!(d.in_flight.contains(&hash(2)));
    }

    #[test]
    fn pop_batch_skips_already_in_flight() {
        let mut d = download(&[hash(1), hash(2), hash(3)], &[hash(2)]);
        assert_eq!(d.pop_batch(3), vec![hash(1), hash(3)]);
    }

    #[test]
    fn pop_batch_returns_partial_when_queue_short() {
        let mut d = download(&[hash(1)], &[]);
        assert_eq!(d.pop_batch(16), vec![hash(1)]);
        assert!(d.queue.is_empty());
    }

    #[test]
    fn pop_batch_returns_empty_when_queue_empty() {
        let mut d = download(&[], &[]);
        assert!(d.pop_batch(16).is_empty());
    }

    #[test]
    fn pop_batch_returns_empty_when_all_in_flight() {
        let mut d = download(&[hash(1), hash(2)], &[hash(1), hash(2)]);
        assert!(d.pop_batch(16).is_empty());
        assert!(d.queue.is_empty());
    }

    #[test]
    fn pop_batch_multiple_calls_drain_queue() {
        let mut d = download(&[hash(1), hash(2), hash(3), hash(4)], &[]);
        assert_eq!(d.pop_batch(2), vec![hash(1), hash(2)]);
        assert_eq!(d.pop_batch(2), vec![hash(3), hash(4)]);
        assert!(d.pop_batch(2).is_empty());
    }

    #[test]
    fn pop_batch_zero_batch_size() {
        let mut d = download(&[hash(1), hash(2)], &[]);
        assert!(d.pop_batch(0).is_empty());
        assert_eq!(d.queue.len(), 2);
    }

    #[test]
    fn pop_batch_preserves_fifo_order() {
        let mut d = download(&[hash(1), hash(2), hash(3), hash(4), hash(5)], &[]);
        assert_eq!(
            d.pop_batch(5),
            vec![hash(1), hash(2), hash(3), hash(4), hash(5)]
        );
    }

    fn long_ago() -> Instant {
        Instant::now() - PEER_STALL_TIMEOUT - Duration::from_secs(1)
    }

    #[test]
    fn stalled_when_awaiting_headers_past_timeout() {
        assert!(stalled(&PeerStateMachine::AwaitingHeaders, long_ago()));
    }

    #[test]
    fn stalled_when_awaiting_block_past_timeout() {
        let state = PeerStateMachine::AwaitingBlock(AwaitingBlock {
            peer_inventory: HashSet::new(),
        });
        assert!(stalled(&state, long_ago()));
    }

    #[test]
    fn not_stalled_when_awaiting_inv() {
        assert!(!stalled(&PeerStateMachine::AwaitingInv, long_ago()));
    }

    #[test]
    fn not_stalled_with_recent_progress() {
        assert!(!stalled(&PeerStateMachine::AwaitingHeaders, Instant::now()));
    }

    #[test]
    fn delivered_when_block_was_requested() {
        let blocks = block_chain(1);
        let state = PeerStateMachine::AwaitingBlock(AwaitingBlock {
            peer_inventory: HashSet::from([blocks[0].block_hash()]),
        });
        assert!(delivers_requested_block(
            &state,
            &NetworkMessage::Block(blocks[0].clone())
        ));
    }

    #[test]
    fn not_delivered_when_block_was_not_requested() {
        let blocks = block_chain(2);
        let state = PeerStateMachine::AwaitingBlock(AwaitingBlock {
            peer_inventory: HashSet::from([blocks[0].block_hash()]),
        });
        assert!(!delivers_requested_block(
            &state,
            &NetworkMessage::Block(blocks[1].clone())
        ));
    }

    #[test]
    fn requeue_unreceived_restores_queue_and_clears_in_flight() {
        let mut d = download(&[hash(5), hash(6)], &[hash(1), hash(2), hash(3)]);
        d.requeue_unreceived(&HashSet::from([hash(1), hash(2)]));
        assert_eq!(d.queue.len(), 4);
        assert!(d.queue.contains(&hash(1)));
        assert!(d.queue.contains(&hash(2)));
        assert!(!d.in_flight.contains(&hash(1)));
        assert!(!d.in_flight.contains(&hash(2)));
        assert!(d.in_flight.contains(&hash(3)));
    }

    #[test]
    fn requeue_unreceived_blocks_can_be_repopped() {
        let mut d = download(&[hash(5)], &[hash(1)]);
        d.requeue_unreceived(&HashSet::from([hash(1)]));
        assert_eq!(d.pop_batch(16), vec![hash(1), hash(5)]);
    }

    #[test]
    fn requeue_unreceived_noop_on_empty() {
        let mut d = download(&[hash(1)], &[hash(2)]);
        d.requeue_unreceived(&HashSet::new());
        assert_eq!(d.queue.len(), 1);
        assert!(d.in_flight.contains(&hash(2)));
    }

    #[derive(Default)]
    struct Connected(HashSet<BlockHash>);

    impl Connected {
        fn connect(&mut self, hash: BlockHash) {
            self.0.insert(hash);
        }

        fn contains(&self) -> impl Fn(&BlockHash) -> bool + '_ {
            move |hash| self.0.contains(hash)
        }
    }

    fn drain(d: &mut DownloadState, connected: &mut Connected) -> Vec<BlockHash> {
        let mut order = Vec::new();
        while let Some(block) = d.take_connectable(connected.contains()) {
            let hash = BlockHash::from_byte_array(block.hash().into());
            connected.connect(hash);
            order.push(hash);
        }
        order
    }

    #[test]
    fn buffer_drains_in_chain_order_despite_out_of_order_arrivals() {
        let genesis = bitcoin::blockdata::constants::genesis_block(Network::Regtest).block_hash();
        let blocks = block_chain(4);
        let expected: Vec<BlockHash> = blocks.iter().map(|b| b.block_hash()).collect();

        let mut d = DownloadState::default();
        for i in [1, 3, 0, 2] {
            d.buffer_block(blocks[i].header.prev_blockhash, blocks[i].clone().convert());
        }

        let mut connected = Connected::default();
        connected.connect(genesis);
        assert_eq!(drain(&mut d, &mut connected), expected);
    }

    #[test]
    fn buffer_holds_blocks_until_parent_arrives() {
        let genesis = bitcoin::blockdata::constants::genesis_block(Network::Regtest).block_hash();
        let blocks = block_chain(2);
        let mut connected = Connected::default();
        connected.connect(genesis);

        // Not idle, so the competing branch path stays shut.
        let mut d = download(&[], &[hash(9)]);
        d.buffer_block(blocks[1].header.prev_blockhash, blocks[1].clone().convert());
        assert!(drain(&mut d, &mut connected).is_empty());

        d.buffer_block(blocks[0].header.prev_blockhash, blocks[0].clone().convert());
        assert_eq!(
            drain(&mut d, &mut connected),
            vec![blocks[0].block_hash(), blocks[1].block_hash()]
        );
    }

    #[test]
    fn buffer_yields_nothing_when_no_parent_is_connected() {
        let blocks = block_chain(2);
        let mut d = download(&[], &[hash(9)]);
        d.buffer_block(blocks[1].header.prev_blockhash, blocks[1].clone().convert());

        assert!(d
            .take_connectable(Connected::default().contains())
            .is_none());
    }

    #[test]
    fn competing_branch_is_released_in_order_once_peers_are_idle() {
        // Nothing here builds on the active chain.
        let blocks = block_chain(4);
        let mut d = DownloadState::default();
        for i in [3, 1, 2] {
            d.buffer_block(blocks[i].header.prev_blockhash, blocks[i].clone().convert());
        }

        assert_eq!(
            drain(&mut d, &mut Connected::default()),
            vec![
                blocks[1].block_hash(),
                blocks[2].block_hash(),
                blocks[3].block_hash()
            ]
        );
    }

    #[test]
    fn competing_branch_waits_while_a_peer_still_owes_blocks() {
        let blocks = block_chain(2);
        let mut d = download(&[], &[hash(9)]);
        d.buffer_block(blocks[1].header.prev_blockhash, blocks[1].clone().convert());

        assert!(d
            .take_connectable(Connected::default().contains())
            .is_none());

        d.release(&hash(9));
        assert!(d
            .take_connectable(Connected::default().contains())
            .is_some());
    }
}
