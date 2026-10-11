use std::{
    collections::HashSet,
    net::{IpAddr, SocketAddr},
    ops::DerefMut,
    sync::{
        atomic::{AtomicBool, Ordering},
        Arc, Mutex,
    },
    thread,
    time::{Duration, Instant},
};

use bitcoin::p2p::{address::AddrV2, message::NetworkMessage, ServiceFlags};
use bitcoin::secp256k1::rand::random;
use bitcoin::{Network, Transaction};
use log::{debug, error, info, warn};
use p2p::{
    handshake::ConnectionConfig,
    net::{ConnectionExt, ConnectionReader, ConnectionWriter, TimeoutParams, READ_TIMEOUT},
};

use crate::{
    logging::Category,
    peer::{BitcoinPeer, NodeState},
    socks5::{OnionAddress, Socks5Proxy},
    FatalShutdown,
};

const TABLE_WIDTH: usize = 16;
const TABLE_SLOT: usize = 16;
const MAX_BUCKETS: usize = 4;

pub type AddrTable = addrman::Table<TABLE_WIDTH, TABLE_SLOT, MAX_BUCKETS>;

const DEFAULT_MAX_PEERS: usize = 8;

/// Consecutive one second waits on an empty address book before giving up.
/// Nothing refills it without a working network, so waiting longer only
/// hides the problem.
const EMPTY_ADDRESS_BOOK_LIMIT: u32 = 60;

const BROADCAST_TIMEOUT: Duration = Duration::from_secs(60);
const BROADCAST_PONG_TIMEOUT: Duration = Duration::from_secs(5);
const FEELER_INTERVAL: Duration = Duration::from_secs(30);

pub struct PeerManager {
    max_peers: usize,
    fatal: FatalShutdown,
    addrman: Arc<Mutex<AddrTable>>,
    node_state: Arc<NodeState>,
    network: Network,
    running: Arc<AtomicBool>,
    peer_threads: Vec<thread::JoinHandle<()>>,
    peer_writers: Vec<Arc<Mutex<Option<Arc<ConnectionWriter>>>>>,
    connected_peers: Arc<Mutex<HashSet<Destination>>>,
    proxy: Option<Socks5Proxy>,
    feeler_thread: Option<thread::JoinHandle<()>>,
}

impl PeerManager {
    pub fn new(
        addrman: Arc<Mutex<AddrTable>>,
        node_state: Arc<NodeState>,
        network: Network,
        fatal: FatalShutdown,
    ) -> Self {
        Self {
            max_peers: DEFAULT_MAX_PEERS,
            fatal,
            addrman,
            node_state,
            network,
            running: Arc::new(AtomicBool::new(true)),
            peer_threads: Vec::new(),
            peer_writers: Vec::new(),
            connected_peers: Arc::new(Mutex::new(HashSet::new())),
            proxy: None,
            feeler_thread: None,
        }
    }

    pub fn set_proxy(&mut self, proxy: Socks5Proxy) {
        self.proxy = Some(proxy);
    }

    pub fn max_peers(mut self, n: usize) -> Self {
        self.max_peers = n.max(1);
        self
    }

    pub fn peer_writers(&self) -> &[Arc<Mutex<Option<Arc<ConnectionWriter>>>>] {
        &self.peer_writers
    }

    pub fn start(&mut self) {
        info!(target: Category::NET, "Starting peer manager with {} peers", self.max_peers);
        for i in 0..self.max_peers {
            let running = Arc::clone(&self.running);
            let addrman = Arc::clone(&self.addrman);
            let node_state = Arc::clone(&self.node_state);
            let network = self.network;
            let writer_slot: Arc<Mutex<Option<Arc<ConnectionWriter>>>> = Arc::new(Mutex::new(None));
            let writer_slot_thread = Arc::clone(&writer_slot);
            self.peer_writers.push(writer_slot);
            let connected_peers = Arc::clone(&self.connected_peers);
            let fatal = self.fatal.clone();
            let proxy = self.proxy.clone();

            let handle = thread::spawn(move || {
                info!(target: Category::NET, "Peer thread {} started", i);
                let mut empty_selections = 0u32;
                while running.load(Ordering::SeqCst) {
                    let selected = {
                        let table = addrman.lock().unwrap();
                        table.select().map(|record| record.network_addr())
                    };
                    let destination = match selected {
                        Some((AddrV2::Ipv4(ipv4), port)) => {
                            Destination::from_socket_addr(SocketAddr::from((ipv4, port)))
                        }
                        Some((AddrV2::Ipv6(ipv6), port)) => {
                            Destination::from_socket_addr(SocketAddr::from((ipv6, port)))
                        }
                        Some((AddrV2::TorV3(pubkey), port)) if proxy.is_some() => {
                            Destination::new(AddrV2::TorV3(pubkey), port)
                        }
                        Some(_) => continue,
                        None => {
                            empty_selections += 1;
                            if empty_selections >= EMPTY_ADDRESS_BOOK_LIMIT {
                                fatal.trigger(
                                    Category::NET,
                                    format!(
                                        "No peer address available for {EMPTY_ADDRESS_BOOK_LIMIT} seconds. \
                                         DNS seeding likely failed and the network is unreachable."
                                    ),
                                );
                                return;
                            }
                            thread::sleep(Duration::from_secs(1));
                            continue;
                        }
                    };
                    empty_selections = 0;

                    {
                        let mut connected = connected_peers.lock().unwrap();
                        if !connected.insert(destination.clone()) {
                            drop(connected);
                            debug!(target: Category::NET, "Peer thread {}: {} already connected", i, destination);
                            thread::sleep(Duration::from_secs(1));
                            continue;
                        }
                    }

                    let mut peer = match BitcoinPeer::new(
                        destination.clone(),
                        proxy.clone(),
                        network,
                        &node_state,
                    ) {
                        Ok(peer) => {
                            *writer_slot_thread.lock().unwrap() = Some(peer.writer());
                            peer
                        }
                        Err(e) => {
                            error!(target: Category::NET, "Peer thread {}: could not connect to {}: {}", i, destination, e);
                            connected_peers.lock().unwrap().remove(&destination);
                            thread::sleep(Duration::from_millis(500));
                            continue;
                        }
                    };

                    info!(target: Category::NET, "Peer thread {}: connected to {}", i, peer);
                    while running.load(Ordering::SeqCst) {
                        if peer.is_stalled() {
                            warn!(target: Category::NET, "Peer thread {}: stalled, disconnecting {}", i, peer);
                            let _ = peer.writer().shutdown();
                            break;
                        }
                        if let Err(e) = peer.receive_and_process_message(&node_state) {
                            match e {
                                p2p::net::Error::Io(io)
                                    if io.kind() == std::io::ErrorKind::UnexpectedEof => {}
                                p2p::net::Error::Io(io) => {
                                    error!(target: Category::NET, "Peer thread {}: I/O error: {}", i, io)
                                }
                                e => {
                                    error!(target: Category::NET, "Peer thread {}: error: {}", i, e)
                                }
                            }
                            break;
                        }
                    }

                    peer.release_in_flight(&node_state.download);
                    connected_peers.lock().unwrap().remove(&destination);
                    *writer_slot_thread.lock().unwrap() = None;
                }
                info!(target: Category::NET, "Peer thread {} stopped", i);
            });
            self.peer_threads.push(handle);
        }

        let running = Arc::clone(&self.running);
        let addrman = Arc::clone(&self.addrman);
        let network = self.network;
        let proxy = self.proxy.clone();
        let handle = thread::spawn(move || {
            info!(target: Category::NODE, "Starting feeler thread.");
            let mut last_feeler = Instant::now();
            while running.load(Ordering::SeqCst) {
                thread::sleep(Duration::from_secs(1));
                if last_feeler.elapsed() < FEELER_INTERVAL {
                    continue;
                }
                open_feeler(&addrman, network, proxy.as_ref());
                last_feeler = Instant::now();
            }
            info!(target: Category::NODE, "Stopping feeler thread.");
        });
        self.feeler_thread = Some(handle);
    }

    pub fn stop(&self) {
        self.running.store(false, Ordering::SeqCst);
        for writer_slot in &self.peer_writers {
            if let Some(conn) = writer_slot.lock().unwrap().deref_mut() {
                let _ = conn.shutdown();
            }
        }
    }

    pub fn join(mut self) {
        for handle in self.peer_threads {
            let _ = handle.join();
        }
        if let Some(handle) = self.feeler_thread.take() {
            let _ = handle.join();
        }
    }

    pub fn broadcaster(&self) -> Broadcaster {
        Broadcaster {
            addrman: Arc::clone(&self.addrman),
            network: self.network,
            proxy: self.proxy.clone(),
        }
    }
}

#[derive(Clone)]
pub struct Broadcaster {
    addrman: Arc<Mutex<AddrTable>>,
    network: Network,
    proxy: Option<Socks5Proxy>,
}

impl Broadcaster {
    pub fn broadcast_transaction(&self, tx: &Transaction) -> bool {
        broadcast_transaction(&self.addrman, self.network, self.proxy.as_ref(), tx)
    }
}

pub(crate) fn connect(
    conf: ConnectionConfig,
    dest: &Destination,
    proxy: Option<&Socks5Proxy>,
    read_timeout: Duration,
) -> Result<(ConnectionWriter, ConnectionReader), p2p::net::Error> {
    let mut timeouts = TimeoutParams::new();
    timeouts.read_timeout(read_timeout);
    match proxy {
        Some(proxy) => {
            let conn = match dest.addr {
                AddrV2::Ipv4(ipv4) => proxy.connect(ipv4, dest.port, read_timeout),
                AddrV2::Ipv6(ipv6) => proxy.connect(ipv6, dest.port, read_timeout),
                AddrV2::TorV3(pubkey) => {
                    proxy.connect(OnionAddress::from_pubkey(pubkey), dest.port, read_timeout)
                }
                _ => {
                    return Err(p2p::net::Error::Io(std::io::Error::other(
                        "cannot connect to destination address",
                    )))
                }
            }
            .map_err(p2p::net::Error::Io)?;
            let (writer, reader, _) = conf.handshake(conn, timeouts)?;
            Ok((writer, reader))
        }
        None => {
            let (writer, reader, _) = match dest.addr {
                AddrV2::Ipv4(ipv4) => conf.open_connection((ipv4, dest.port), timeouts)?,
                AddrV2::Ipv6(ipv6) => conf.open_connection((ipv6, dest.port), timeouts)?,
                _ => {
                    return Err(p2p::net::Error::Io(std::io::Error::other(
                        "cannot connect to destination address without a proxy",
                    )))
                }
            };
            Ok((writer, reader))
        }
    }
}

fn open_feeler(addrman: &Mutex<AddrTable>, network: Network, proxy: Option<&Socks5Proxy>) {
    let Some(record) = addrman.lock().unwrap().select() else {
        return;
    };
    let (addr, port) = record.network_addr();
    let dest = Destination { addr, port };
    let conf = ConnectionConfig::new()
        .change_network(network)
        .set_service_requirement(ServiceFlags::NETWORK)
        .offer_services(ServiceFlags::WITNESS)
        .user_agent("/kernel-node:0.1.0/".into());
    match connect(conf, &dest, proxy, READ_TIMEOUT) {
        Ok(_) => {
            info!(target: Category::NODE, "Successful feeler connection opened to {}", dest);
            addrman.lock().unwrap().successful_connection(&record);
        }
        Err(_) => {
            info!(target: Category::NODE, "Failed feeler connection to {}", dest);
            addrman.lock().unwrap().failed_connection(&record);
        }
    }
}

fn broadcast_transaction(
    addrman: &Mutex<AddrTable>,
    network: Network,
    proxy: Option<&Socks5Proxy>,
    tx: &Transaction,
) -> bool {
    let txid = tx.compute_txid();
    let start = Instant::now();
    while start.elapsed() < BROADCAST_TIMEOUT {
        let Some(record) = addrman.lock().unwrap().select() else {
            break;
        };
        let (addr, port) = record.network_addr();
        let dest = Destination { addr, port };
        let conf = ConnectionConfig::new()
            .change_network(network)
            .offer_services(ServiceFlags::WITNESS)
            .user_agent("/kernel-node:0.1.0/".into());
        match connect(conf, &dest, proxy, Duration::from_secs(1)) {
            Ok((writer, mut reader)) => match writer.send_message(NetworkMessage::Tx(tx.clone())) {
                Ok(_) => {
                    let nonce: u64 = random();
                    if let Err(e) = writer.send_message(NetworkMessage::Ping(nonce)) {
                        warn!(target: Category::NODE, "Failed to ping {} after sending {}: {}", dest, txid, e);
                    } else if wait_for_pong(&mut reader, nonce) {
                        info!(target: Category::NODE, "Broadcast transaction {} to {}", txid, dest);
                        addrman.lock().unwrap().successful_connection(&record);
                        return true;
                    } else {
                        warn!(target: Category::NODE, "No pong from {} confirming {}", dest, txid);
                    }
                }
                Err(e) => {
                    warn!(target: Category::NODE, "Failed to send transaction to {}: {}", dest, e);
                }
            },
            Err(_) => {
                info!(target: Category::NODE, "Failed broadcast connection to {}", dest);
                addrman.lock().unwrap().failed_connection(&record);
            }
        }
    }
    warn!(target: Category::NODE, "Failed to broadcast transaction {}", txid);
    false
}

fn wait_for_pong(reader: &mut ConnectionReader, nonce: u64) -> bool {
    let deadline = Instant::now() + BROADCAST_PONG_TIMEOUT;
    while Instant::now() < deadline {
        match reader.read_message() {
            Ok(Some(NetworkMessage::Pong(received))) if received == nonce => return true,
            Ok(_) => continue,
            Err(p2p::net::Error::Io(e))
                if e.kind() == std::io::ErrorKind::WouldBlock
                    || e.kind() == std::io::ErrorKind::TimedOut =>
            {
                continue
            }
            Err(_) => return false,
        }
    }
    false
}

#[derive(Debug, Clone, PartialEq, Eq, std::hash::Hash)]
pub struct Destination {
    pub addr: AddrV2,
    pub port: u16,
}

impl Destination {
    pub fn new(addr: AddrV2, port: u16) -> Self {
        Self { addr, port }
    }

    pub fn from_socket_addr(socket_addr: SocketAddr) -> Self {
        match socket_addr.ip() {
            IpAddr::V4(ipv4) => Destination {
                addr: AddrV2::Ipv4(ipv4),
                port: socket_addr.port(),
            },
            IpAddr::V6(ipv6) => Destination {
                addr: AddrV2::Ipv6(ipv6),
                port: socket_addr.port(),
            },
        }
    }
}

impl core::fmt::Display for Destination {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.addr {
            AddrV2::Ipv4(ipv4) => write!(f, "{}:{}", ipv4, self.port),
            AddrV2::Ipv6(ipv6) => write!(f, "{}:{}", ipv6, self.port),
            AddrV2::TorV3(torv3) => write!(f, "{}:{}", OnionAddress::from_pubkey(torv3), self.port),
            _ => write!(f, "unreachable address"),
        }
    }
}
