// Embedded FuturChain Rust runtime — bundled into fl.js by esbuild.
// `fl chain` writes these to ~/.futurlang/chain/ and compiles once.

export const CHAIN_CARGO_TOML = `\
[package]
name = "futurchain"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "futurchain"
path = "src/main.rs"

[lib]
name = "futurchain"
path = "src/lib.rs"

[dependencies]
tokio         = { version = "1",  features = ["full"] }
axum          = "0.7"
serde         = { version = "1",  features = ["derive"] }
serde_json    = "1"
sha2          = "0.10"
hex           = "0.4"
ed25519-dalek = { version = "2",  features = ["rand_core"] }
rand          = "0.8"
thiserror     = "1"
clap          = { version = "4",  features = ["derive"] }
anyhow        = "1"
sled          = "0.34"

[dev-dependencies]
tokio-test    = "0.4"
`;

export const CHAIN_SRC: Record<string, string> = {
  'main.rs': `\
use std::sync::{Arc, Mutex};
use tokio::time::{interval, Duration};
use clap::Parser;
use futurchain::{chain::Chain, crypto::Keypair, mempool::Mempool, rpc, types::hex_address};

#[derive(Parser)]
#[command(name = "futurchain", about = "FuturChain node — Solana-inspired blockchain")]
struct Cli {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,

    #[arg(long, default_value_t = 8899)]
    port: u16,

    #[arg(long, default_value_t = 400)]
    slot_ms: u64,

    #[arg(long, default_value_t = 1000)]
    block_size: usize,

    #[arg(long, default_value_t = 1_000_000_000)]
    genesis_supply: u64,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let keypair   = Keypair::generate();
    let node_addr = keypair.address();
    println!("══════════════════════════════════════════════════════════════════");
    println!("  FuturChain Node");
    println!("  Address : {}", hex_address(&node_addr));
    println!("  RPC     : http://{}:{}", cli.host, cli.port);
    println!("  Slot    : {}ms", cli.slot_ms);
    println!("══════════════════════════════════════════════════════════════════");

    let chain   = Arc::new(Mutex::new(Chain::new()));
    let mempool = Arc::new(Mutex::new(Mempool::new(100_000)));

    {
        let mut c = chain.lock().unwrap();
        c.ledger.airdrop(node_addr, cli.genesis_supply);
        println!("Genesis: {} tokens → {}", cli.genesis_supply, hex_address(&node_addr));
    }

    let chain_bg   = chain.clone();
    let mempool_bg = mempool.clone();
    let block_size = cli.block_size;
    tokio::spawn(async move {
        let mut ticker = interval(Duration::from_millis(cli.slot_ms));
        loop {
            ticker.tick().await;
            let txs   = mempool_bg.lock().unwrap().drain(block_size);
            let block = chain_bg.lock().unwrap().produce_block(txs, node_addr);
            if block.header.tx_count > 0 || block.header.slot % 10 == 0 {
                println!(
                    "slot {:>6} | txs {:>4} | poh {}…",
                    block.header.slot,
                    block.header.tx_count,
                    hex::encode(&block.hash[..4])
                );
            }
        }
    });

    let addr     = format!("{}:{}", cli.host, cli.port);
    let app      = rpc::router(chain, mempool);
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    println!("RPC listening — Ctrl+C to stop\\n");
    axum::serve(listener, app).await?;
    Ok(())
}
`,

  'lib.rs': `\
pub mod chain;
pub mod crypto;
pub mod ledger;
pub mod mempool;
pub mod rpc;
pub mod types;

pub mod prelude {
    pub use crate::types::*;
    pub use crate::crypto::{sha256, poh_tick, verify_signature, pda_derive, find_pda};
    pub use serde::{Serialize, Deserialize};

    pub type Result<T> = std::result::Result<T, ProgramError>;

    #[derive(Debug, thiserror::Error)]
    pub enum ProgramError {
        #[error("account not found at index {0}")]
        AccountNotFound(usize),
        #[error("not a signer")]
        NotSigner,
        #[error("insufficient funds")]
        InsufficientFunds,
        #[error("arithmetic overflow")]
        Overflow,
        #[error("account is not writable")]
        NotWritable,
        #[error("invalid PDA seeds")]
        InvalidSeeds,
        #[error("cpi error: {0}")]
        CpiError(String),
        #[error("{0}")]
        Custom(String),
    }

    impl From<&str> for ProgramError { fn from(s: &str) -> Self { ProgramError::Custom(s.to_string()) } }
    impl From<String> for ProgramError { fn from(s: String) -> Self { ProgramError::Custom(s) } }

    #[derive(Debug, Clone, Copy)]
    pub struct Clock { pub slot: Slot, pub timestamp: u64 }

    #[derive(Debug, Clone)]
    pub struct AccountInfo {
        pub address: Address, pub balance: TokenAmount,
        pub is_signer: bool, pub is_writable: bool,
        pub owner: Address, pub data: Vec<u8>,
    }

    impl AccountInfo {
        pub fn deserialize<T: for<'de> serde::Deserialize<'de>>(&self) -> Result<T> {
            serde_json::from_slice(&self.data).map_err(|e| ProgramError::Custom(e.to_string()))
        }
        pub fn serialize<T: serde::Serialize>(&mut self, state: &T) -> Result<()> {
            self.data = serde_json::to_vec(state).map_err(|e| ProgramError::Custom(e.to_string()))?;
            Ok(())
        }
    }

    pub struct CpiInstruction { pub program_id: Address, pub accounts: Vec<AccountInfo>, pub data: Vec<u8> }
    pub struct EmittedEvent   { pub name: String, pub data: Vec<u8> }

    pub struct Context {
        pub program_id: Address, pub accounts: Vec<AccountInfo>,
        pub clock: Clock, pub events: Vec<EmittedEvent>, pub cpi_calls: Vec<CpiInstruction>,
    }

    impl Context {
        pub fn new(program_id: Address, accounts: Vec<AccountInfo>, slot: Slot, timestamp: u64) -> Self {
            Self { program_id, accounts, clock: Clock { slot, timestamp }, events: vec![], cpi_calls: vec![] }
        }
        pub fn signer(&self, idx: usize) -> Result<Address> {
            let acc = self.accounts.get(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_signer { return Err(ProgramError::NotSigner); }
            Ok(acc.address)
        }
        pub fn account(&self, idx: usize) -> Result<&AccountInfo> {
            self.accounts.get(idx).ok_or(ProgramError::AccountNotFound(idx))
        }
        pub fn account_mut(&mut self, idx: usize) -> Result<&mut AccountInfo> {
            let acc = self.accounts.get_mut(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_writable { return Err(ProgramError::NotWritable); }
            Ok(acc)
        }
        pub fn load<T: for<'de> serde::Deserialize<'de>>(&self, idx: usize) -> Result<T> {
            self.account(idx)?.deserialize::<T>()
        }
        pub fn save<T: serde::Serialize>(&mut self, idx: usize, state: &T) -> Result<()> {
            let acc = self.accounts.get_mut(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_writable { return Err(ProgramError::NotWritable); }
            acc.serialize(state)
        }
        pub fn pda(&self, seeds: &[&[u8]]) -> Address { pda_derive(seeds, &self.program_id) }
        pub fn emit(&mut self, name: &str, data: Vec<u8>) {
            self.events.push(EmittedEvent { name: name.to_string(), data });
        }
        pub fn cpi(&mut self, ix: CpiInstruction) { self.cpi_calls.push(ix); }
        pub fn transfer(&mut self, from_idx: usize, to_idx: usize, amount: TokenAmount) -> Result<()> {
            let from_bal = {
                let from = self.accounts.get(from_idx).ok_or(ProgramError::AccountNotFound(from_idx))?;
                if !from.is_writable { return Err(ProgramError::NotWritable); }
                from.balance
            };
            if from_bal < amount { return Err(ProgramError::InsufficientFunds); }
            self.accounts[from_idx].balance -= amount;
            let to = self.accounts.get_mut(to_idx).ok_or(ProgramError::AccountNotFound(to_idx))?;
            to.balance = to.balance.checked_add(amount).ok_or(ProgramError::Overflow)?;
            Ok(())
        }
    }

    pub trait Program { fn process(ctx: &mut Context, data: &[u8]) -> Result<()>; }

    #[macro_export]
    macro_rules! require {
        ($cond:expr, $err:expr) => { if !($cond) { return Err($err.into()); } };
    }
    #[macro_export]
    macro_rules! emit {
        ($ctx:expr, $name:expr, $data:expr) => {{
            let bytes = serde_json::to_vec($data).unwrap_or_default();
            $ctx.emit($name, bytes);
        }};
    }
}

pub mod runtime {
    pub use crate::chain::Chain;
    pub use crate::crypto::{poh_tick, sha256, pda_derive, find_pda, Keypair};
    pub use crate::ledger::{Ledger, LedgerError};
    pub use crate::mempool::Mempool;
    pub use crate::types::*;
}
`,

  'types.rs': `\
use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub type Hash        = [u8; 32];
pub type Address     = [u8; 32];
pub type Signature   = [u8; 64];
pub type Slot        = u64;
pub type Epoch       = u64;
pub type TokenAmount = u64;

pub mod serde_addr {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("address must be 32 bytes"))
    }
}

pub mod serde_hash {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("hash must be 32 bytes"))
    }
}

pub mod serde_sig {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 64], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 64], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("signature must be 64 bytes"))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Account {
    #[serde(with = "serde_addr")]
    pub address:    Address,
    pub balance:    TokenAmount,
    pub nonce:      u64,
    pub data:       Vec<u8>,
    #[serde(with = "serde_addr")]
    pub owner:      Address,
    pub executable: bool,
}

impl Account {
    pub fn new(address: Address) -> Self {
        Self { address, balance: 0, nonce: 0, data: vec![], owner: [0u8; 32], executable: false }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccountMeta {
    #[serde(with = "serde_addr")]
    pub address:     Address,
    pub is_signer:   bool,
    pub is_writable: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Instruction {
    #[serde(with = "serde_addr")]
    pub program_id: Address,
    pub accounts:   Vec<AccountMeta>,
    pub data:       Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub nonce:             u64,
    #[serde(with = "serde_addr")]
    pub sender:            Address,
    #[serde(with = "serde_addr")]
    pub recipient:         Address,
    pub amount:            TokenAmount,
    pub fee:               TokenAmount,
    pub instructions:      Vec<Instruction>,
    #[serde(with = "serde_hash")]
    pub recent_blockhash:  Hash,
    #[serde(with = "serde_sig")]
    pub signature:         Signature,
}

impl Transaction {
    pub fn signable_bytes(&self) -> Vec<u8> {
        let mut b = Vec::new();
        b.extend_from_slice(&self.nonce.to_le_bytes());
        b.extend_from_slice(&self.sender);
        b.extend_from_slice(&self.recipient);
        b.extend_from_slice(&self.amount.to_le_bytes());
        b.extend_from_slice(&self.fee.to_le_bytes());
        b.extend_from_slice(&self.recent_blockhash);
        b
    }
    pub fn hash(&self) -> Hash {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(self.signable_bytes());
        h.update(self.signature);
        h.finalize().into()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    #[serde(with = "serde_addr")]
    pub program_id: Address,
    pub name:       String,
    pub data:       Vec<u8>,
    pub slot:       Slot,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockHeader {
    pub slot:          Slot,
    #[serde(with = "serde_hash")]
    pub parent_hash:   Hash,
    #[serde(with = "serde_hash")]
    pub poh_hash:      Hash,
    #[serde(with = "serde_hash")]
    pub tx_root:       Hash,
    #[serde(with = "serde_hash")]
    pub state_root:    Hash,
    #[serde(with = "serde_addr")]
    pub proposer:      Address,
    pub timestamp:     u64,
    pub tx_count:      u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    pub header:       BlockHeader,
    pub transactions: Vec<Transaction>,
    pub events:       Vec<Event>,
    #[serde(with = "serde_hash")]
    pub hash:         Hash,
}

impl Block {
    pub fn compute_hash(header: &BlockHeader) -> Hash {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(header.slot.to_le_bytes());
        h.update(header.parent_hash);
        h.update(header.poh_hash);
        h.update(header.tx_root);
        h.update(header.state_root);
        h.update(header.proposer);
        h.update(header.timestamp.to_le_bytes());
        h.finalize().into()
    }
    pub fn genesis() -> Self {
        let header = BlockHeader {
            slot: 0, parent_hash: [0u8; 32], poh_hash: [0u8; 32],
            tx_root: [0u8; 32], state_root: [0u8; 32], proposer: [0u8; 32],
            timestamp: 0, tx_count: 0,
        };
        let hash = Self::compute_hash(&header);
        Self { header, transactions: vec![], events: vec![], hash }
    }
}

pub fn hex_address(addr: &Address) -> String { hex::encode(addr) }
pub fn hex_hash(h: &Hash) -> String { hex::encode(h) }
`,

  'crypto.rs': `\
use crate::types::{Address, Hash, Signature};
use ed25519_dalek::{Signer, Verifier, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256};

pub fn sha256(data: &[u8]) -> Hash {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize().into()
}

pub fn poh_tick(prev: Hash) -> Hash { sha256(&prev) }

pub fn hash_transactions(txs: &[crate::types::Transaction]) -> Hash {
    if txs.is_empty() { return [0u8; 32]; }
    let mut h = Sha256::new();
    for tx in txs { h.update(tx.hash()); }
    h.finalize().into()
}

pub struct Keypair { inner: SigningKey }

impl Keypair {
    pub fn generate() -> Self { Self { inner: SigningKey::generate(&mut rand::rngs::OsRng) } }
    pub fn from_secret_bytes(bytes: &[u8; 32]) -> Self { Self { inner: SigningKey::from_bytes(bytes) } }
    pub fn address(&self) -> Address { self.inner.verifying_key().to_bytes() }
    pub fn sign(&self, data: &[u8]) -> Signature { self.inner.sign(data).to_bytes() }
    pub fn secret_bytes(&self) -> [u8; 32] { self.inner.to_bytes() }
}

pub fn pda_derive(seeds: &[&[u8]], program_id: &Address) -> Address {
    let mut h = Sha256::new();
    for seed in seeds { h.update(seed); }
    h.update(program_id);
    h.update(b"pda");
    h.finalize().into()
}

pub fn find_pda(seeds: &[&[u8]], program_id: &Address) -> (Address, u8) {
    for bump in (0u8..=255).rev() {
        let mut all_seeds: Vec<&[u8]> = seeds.to_vec();
        let bump_bytes = [bump];
        all_seeds.push(&bump_bytes);
        let addr = pda_derive(&all_seeds, program_id);
        return (addr, bump);
    }
    (pda_derive(seeds, program_id), 0)
}

pub fn verify_signature(address: &Address, data: &[u8], sig: &Signature) -> bool {
    let Ok(vk) = VerifyingKey::from_bytes(address) else { return false; };
    let dalek_sig = ed25519_dalek::Signature::from_bytes(sig);
    vk.verify(data, &dalek_sig).is_ok()
}
`,

  'ledger.rs': `\
use std::collections::HashMap;
use crate::types::{Account, Address, Hash, TokenAmount, Transaction};
use crate::crypto;
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LedgerError {
    #[error("account not found")]
    AccountNotFound,
    #[error("insufficient balance: need {need}, have {have}")]
    InsufficientBalance { need: u64, have: u64 },
    #[error("invalid nonce: expected {expected}, got {got}")]
    InvalidNonce { expected: u64, got: u64 },
    #[error("invalid signature")]
    InvalidSignature,
    #[error("arithmetic overflow")]
    Overflow,
}

pub struct Ledger { accounts: HashMap<Address, Account> }

impl Ledger {
    pub fn new() -> Self { Self { accounts: HashMap::new() } }
    pub fn get(&self, address: &Address) -> Option<&Account> { self.accounts.get(address) }
    pub fn airdrop(&mut self, address: Address, amount: TokenAmount) {
        self.accounts.entry(address).or_insert_with(|| Account::new(address)).balance += amount;
    }
    pub fn apply_transaction(&mut self, tx: &Transaction) -> Result<(), LedgerError> {
        if !crypto::verify_signature(&tx.sender, &tx.signable_bytes(), &tx.signature) {
            return Err(LedgerError::InvalidSignature);
        }
        let (expected_nonce, sender_balance) = self.accounts.get(&tx.sender)
            .map(|a| (a.nonce, a.balance)).unwrap_or((0, 0));
        if tx.nonce != expected_nonce {
            return Err(LedgerError::InvalidNonce { expected: expected_nonce, got: tx.nonce });
        }
        let total = tx.amount.checked_add(tx.fee).ok_or(LedgerError::Overflow)?;
        if sender_balance < total {
            return Err(LedgerError::InsufficientBalance { need: total, have: sender_balance });
        }
        { let s = self.accounts.entry(tx.sender).or_insert_with(|| Account::new(tx.sender)); s.balance -= total; s.nonce += 1; }
        { let r = self.accounts.entry(tx.recipient).or_insert_with(|| Account::new(tx.recipient)); r.balance = r.balance.checked_add(tx.amount).ok_or(LedgerError::Overflow)?; }
        Ok(())
    }
    pub fn state_root(&self) -> Hash {
        let mut addresses: Vec<Address> = self.accounts.keys().copied().collect();
        addresses.sort();
        let mut h = Sha256::new();
        for addr in addresses {
            let acc = &self.accounts[&addr];
            h.update(addr); h.update(acc.balance.to_le_bytes()); h.update(acc.nonce.to_le_bytes());
        }
        h.finalize().into()
    }
    pub fn total_supply(&self) -> TokenAmount { self.accounts.values().map(|a| a.balance).sum() }
    pub fn account_count(&self) -> usize { self.accounts.len() }
}
`,

  'chain.rs': `\
use crate::crypto;
use crate::ledger::Ledger;
use crate::types::{Address, Block, BlockHeader, Event, Hash, Slot, Transaction};

pub struct Chain {
    pub blocks:    Vec<Block>,
    pub ledger:    Ledger,
    pub slot:      Slot,
    pub poh_hash:  Hash,
    pub event_log: Vec<Event>,
}

impl Chain {
    pub fn new() -> Self {
        let genesis  = Block::genesis();
        let poh_hash = genesis.header.poh_hash;
        Self { blocks: vec![genesis], ledger: Ledger::new(), slot: 0, poh_hash, event_log: vec![] }
    }
    pub fn tip_hash(&self) -> Hash { self.blocks.last().map(|b| b.hash).unwrap_or([0u8; 32]) }
    pub fn get_block(&self, slot: Slot) -> Option<&Block> { self.blocks.get(slot as usize) }
    pub fn produce_block(&mut self, transactions: Vec<Transaction>, proposer: Address) -> Block {
        self.slot    += 1;
        self.poh_hash = crypto::poh_tick(self.poh_hash);
        let parent_hash = self.tip_hash();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_secs();
        let mut valid_txs = Vec::new();
        for tx in transactions {
            if self.ledger.apply_transaction(&tx).is_ok() { valid_txs.push(tx); }
        }
        let tx_root    = crypto::hash_transactions(&valid_txs);
        let state_root = self.ledger.state_root();
        let header = BlockHeader {
            slot: self.slot, parent_hash, poh_hash: self.poh_hash,
            tx_root, state_root, proposer, timestamp, tx_count: valid_txs.len() as u32,
        };
        let hash  = Block::compute_hash(&header);
        let block = Block { header, transactions: valid_txs, events: vec![], hash };
        self.blocks.push(block.clone());
        block
    }
    pub fn height(&self) -> usize { self.blocks.len() }
    pub fn events_at_slot(&self, slot: Slot) -> &[Event] {
        self.blocks.get(slot as usize).map(|b| b.events.as_slice()).unwrap_or(&[])
    }
    pub fn recent_events(&self, limit: usize) -> Vec<&Event> {
        self.event_log.iter().rev().take(limit).collect()
    }
}
`,

  'mempool.rs': `\
use std::collections::{HashMap, VecDeque};
use crate::types::{Hash, Transaction};

pub struct Mempool { queue: VecDeque<Transaction>, seen: HashMap<Hash, bool>, max_size: usize }

impl Mempool {
    pub fn new(max_size: usize) -> Self { Self { queue: VecDeque::new(), seen: HashMap::new(), max_size } }
    pub fn push(&mut self, tx: Transaction) -> bool {
        if self.queue.len() >= self.max_size { return false; }
        let h = tx.hash();
        if self.seen.contains_key(&h) { return false; }
        self.seen.insert(h, true);
        self.queue.push_back(tx);
        true
    }
    pub fn drain(&mut self, max: usize) -> Vec<Transaction> {
        let count = max.min(self.queue.len());
        self.queue.drain(..count).collect()
    }
    pub fn len(&self) -> usize { self.queue.len() }
    pub fn is_empty(&self) -> bool { self.queue.is_empty() }
}
`,

  'rpc.rs': `\
use std::sync::{Arc, Mutex};
use axum::{
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};
use crate::{chain::Chain, mempool::Mempool, types::*};

pub type SharedChain   = Arc<Mutex<Chain>>;
pub type SharedMempool = Arc<Mutex<Mempool>>;
pub type AppState      = (SharedChain, SharedMempool);

#[derive(Serialize)]
pub struct HealthResponse { pub status: &'static str, pub slot: Slot, pub block_height: usize, pub total_supply: TokenAmount, pub pending_txs: usize }

#[derive(Serialize)]
pub struct SlotResponse { pub slot: Slot, pub poh_hash: String }

#[derive(Serialize)]
pub struct AccountResponse { pub address: String, pub balance: TokenAmount, pub nonce: u64 }

#[derive(Deserialize)]
pub struct SubmitTxRequest { pub transaction: Transaction }

#[derive(Serialize)]
pub struct SubmitTxResponse { pub accepted: bool, pub tx_hash: String, pub reason: Option<String> }

#[derive(Serialize)]
pub struct EventResponse { pub slot: Slot, pub program_id: String, pub name: String, pub data_hex: String }

#[derive(Deserialize)]
pub struct PdaRequest { pub seeds: Vec<String>, pub program_id: String }

#[derive(Serialize)]
pub struct PdaResponse { pub address: String, pub bump: u8 }

pub fn router(chain: SharedChain, mempool: SharedMempool) -> Router {
    Router::new()
        .route("/health",           get(health))
        .route("/slot",             get(current_slot))
        .route("/block/:slot",      get(get_block))
        .route("/account/:address", get(get_account))
        .route("/transaction",      post(submit_tx))
        .route("/events",           get(get_recent_events))
        .route("/events/:slot",     get(get_events_at_slot))
        .route("/pda",              post(derive_pda))
        .with_state((chain, mempool))
}

async fn health(State((chain, mempool)): State<AppState>) -> Json<HealthResponse> {
    let c = chain.lock().unwrap(); let m = mempool.lock().unwrap();
    Json(HealthResponse { status: "ok", slot: c.slot, block_height: c.height(), total_supply: c.ledger.total_supply(), pending_txs: m.len() })
}

async fn current_slot(State((chain, _)): State<AppState>) -> Json<SlotResponse> {
    let c = chain.lock().unwrap();
    Json(SlotResponse { slot: c.slot, poh_hash: hex_hash(&c.poh_hash) })
}

async fn get_block(State((chain, _)): State<AppState>, Path(slot): Path<u64>) -> Result<Json<Block>, (StatusCode, String)> {
    let c = chain.lock().unwrap();
    c.get_block(slot).cloned().map(Json).ok_or((StatusCode::NOT_FOUND, format!("block {slot} not found")))
}

async fn get_account(State((chain, _)): State<AppState>, Path(address_hex): Path<String>) -> Result<Json<AccountResponse>, (StatusCode, String)> {
    let bytes = hex::decode(&address_hex).map_err(|_| (StatusCode::BAD_REQUEST, "address must be hex".into()))?;
    if bytes.len() != 32 { return Err((StatusCode::BAD_REQUEST, "address must be 32 bytes (64 hex chars)".into())); }
    let mut addr = [0u8; 32]; addr.copy_from_slice(&bytes);
    let c = chain.lock().unwrap();
    c.ledger.get(&addr).map(|a| Json(AccountResponse { address: hex_address(&a.address), balance: a.balance, nonce: a.nonce }))
        .ok_or((StatusCode::NOT_FOUND, "account not found".into()))
}

async fn submit_tx(State((_, mempool)): State<AppState>, Json(req): Json<SubmitTxRequest>) -> Json<SubmitTxResponse> {
    let tx_hash = hex_hash(&req.transaction.hash());
    let accepted = mempool.lock().unwrap().push(req.transaction);
    Json(SubmitTxResponse { accepted, tx_hash, reason: if accepted { None } else { Some("mempool full or duplicate".into()) } })
}

async fn get_recent_events(State((chain, _)): State<AppState>) -> Json<Vec<EventResponse>> {
    let c = chain.lock().unwrap();
    Json(c.recent_events(50).into_iter().map(event_to_resp).collect())
}

async fn get_events_at_slot(State((chain, _)): State<AppState>, Path(slot): Path<u64>) -> Json<Vec<EventResponse>> {
    let c = chain.lock().unwrap();
    Json(c.events_at_slot(slot).iter().map(event_to_resp).collect())
}

async fn derive_pda(State((_, _)): State<AppState>, Json(req): Json<PdaRequest>) -> Result<Json<PdaResponse>, (StatusCode, String)> {
    use crate::crypto::find_pda;
    let prog_bytes = hex::decode(&req.program_id).map_err(|_| (StatusCode::BAD_REQUEST, "program_id must be hex".into()))?;
    if prog_bytes.len() != 32 { return Err((StatusCode::BAD_REQUEST, "program_id must be 32 bytes".into())); }
    let mut program_id = [0u8; 32]; program_id.copy_from_slice(&prog_bytes);
    let decoded_seeds: Result<Vec<Vec<u8>>, _> = req.seeds.iter().map(|s| hex::decode(s)).collect();
    let decoded_seeds = decoded_seeds.map_err(|_| (StatusCode::BAD_REQUEST, "seeds must be hex-encoded".into()))?;
    let seed_slices: Vec<&[u8]> = decoded_seeds.iter().map(|v| v.as_slice()).collect();
    let (addr, bump) = find_pda(&seed_slices, &program_id);
    Ok(Json(PdaResponse { address: hex_address(&addr), bump }))
}

fn event_to_resp(e: &crate::types::Event) -> EventResponse {
    EventResponse { slot: e.slot, program_id: hex_address(&e.program_id), name: e.name.clone(), data_hex: hex::encode(&e.data) }
}
`,
};

// Stable hash of all source files — used to detect when a rebuild is needed
export const CHAIN_SOURCE_HASH: string = (() => {
  const all = CHAIN_CARGO_TOML + Object.entries(CHAIN_SRC).sort().map(([k, v]) => k + v).join('');
  let h = 0;
  for (let i = 0; i < all.length; i++) { h = (Math.imul(31, h) + all.charCodeAt(i)) | 0; }
  return (h >>> 0).toString(16);
})();
