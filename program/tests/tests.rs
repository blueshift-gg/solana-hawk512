use mollusk_svm::Mollusk;
use solana_account::Account;
use solana_address::Address;
use solana_instruction::{AccountMeta, Instruction};

// Static fixture — a fixed (pubkey, signature, message) HAWK-512 triple from
// the reference vector set, baked into the repo for deterministic CU
// measurement. `hawk.prepared` is the same pubkey precomputed into the
// crate-specific prepared form (regenerate with
// `cargo test -p host-tests --test regen_prepared -- --ignored`).
//
// Instruction data is `[mode: 1][payload]`:
//   mode 0 (raw):      payload = [pubkey: 1024][signature: 555][message]
//   mode 1 (prepared): payload = [signature: 555][message]  (pubkey baked in)
//   mode 2 (register): payload = [pubkey: 1024]  (+ 1 writable account)
const PK: &[u8] = include_bytes!("fixtures/hawk.pk");
const SIG: &[u8] = include_bytes!("fixtures/hawk.sig");
const MSG: &[u8] = include_bytes!("fixtures/hawk.msg");
// The same pubkey prepared on the host — the on-chain `mode = 2` path must
// reproduce these exact bytes (consensus-critical bit-for-bit equality).
const PREPARED: &[u8] = include_bytes!("fixtures/hawk.prepared");

fn raw_ix(pk: &[u8], sig: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut d = Vec::with_capacity(1 + pk.len() + sig.len() + msg.len());
    d.push(0); // mode 0: raw pubkey
    d.extend_from_slice(pk);
    d.extend_from_slice(sig);
    d.extend_from_slice(msg);
    d
}

fn prepared_ix(sig: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut d = Vec::with_capacity(1 + sig.len() + msg.len());
    d.push(1); // mode 1: baked-in prepared pubkey
    d.extend_from_slice(sig);
    d.extend_from_slice(msg);
    d
}

fn make_mollusk() -> (Mollusk, Address) {
    let program_id = Address::new_unique();
    // `cargo test-sbf` sets SBF_OUT_DIR; Mollusk loads the .so from there.
    let mut mollusk = Mollusk::new(&program_id, "../target/deploy/program");
    // Raise the CU ceiling far above the on-chain 1.4M cap so we can
    // *measure* the true cost of each path.
    mollusk.compute_budget.compute_unit_limit = 10_000_000;
    (mollusk, program_id)
}

fn run(data: Vec<u8>) -> mollusk_svm::result::InstructionResult {
    let (mollusk, program_id) = make_mollusk();
    let ix = Instruction {
        program_id,
        accounts: vec![],
        data,
    };
    mollusk.process_instruction(&ix, &[])
}

#[test]
fn raw_verify_fixed_vector() {
    let r = run(raw_ix(PK, SIG, MSG));
    assert!(
        !r.program_result.is_err(),
        "raw verify failed: {:?}",
        r.program_result
    );
    println!(
        "raw verify OK — compute units consumed: {}",
        r.compute_units_consumed
    );
}

#[test]
fn prepared_verify_fixed_vector() {
    let r = run(prepared_ix(SIG, MSG));
    assert!(
        !r.program_result.is_err(),
        "prepared verify failed: {:?}",
        r.program_result
    );
    println!(
        "prepared verify OK — compute units consumed: {}",
        r.compute_units_consumed
    );
}

#[test]
fn raw_rejects_tampered_message() {
    let mut m = MSG.to_vec();
    m[0] ^= 0x01;
    assert!(
        run(raw_ix(PK, SIG, &m)).program_result.is_err(),
        "expected failure on tampered message (raw)"
    );
}

#[test]
fn prepared_rejects_tampered_message() {
    let mut m = MSG.to_vec();
    m[0] ^= 0x01;
    assert!(
        run(prepared_ix(SIG, &m)).program_result.is_err(),
        "expected failure on tampered message (prepared)"
    );
}

#[test]
fn raw_rejects_tampered_signature() {
    let mut sig = SIG.to_vec();
    sig[40] ^= 0x01; // past the 24-byte salt, inside s1
    assert!(
        run(raw_ix(PK, &sig, MSG)).program_result.is_err(),
        "expected failure on tampered signature (raw)"
    );
}

#[test]
fn prepared_rejects_tampered_signature() {
    let mut sig = SIG.to_vec();
    sig[40] ^= 0x01;
    assert!(
        run(prepared_ix(&sig, MSG)).program_result.is_err(),
        "expected failure on tampered signature (prepared)"
    );
}

// ---- mode 2: on-chain registration (prepare into an account) -------------

fn register_ix(pk: &[u8]) -> Vec<u8> {
    let mut d = Vec::with_capacity(1 + pk.len());
    d.push(2); // mode 2: prepare `pk` into the writable account
    d.extend_from_slice(pk);
    d
}

/// Run `mode = 2` against one writable, program-owned account sized for the
/// prepared blob; returns the result and the account key.
fn run_register(pk: &[u8]) -> (mollusk_svm::result::InstructionResult, Address) {
    let (mollusk, program_id) = make_mollusk();
    let acct_key = Address::new_unique();
    // Zeroed account data, exactly the prepared-blob size, owned by the
    // program so the runtime lets it write the result back.
    let account = Account::new(1_000_000_000, PREPARED.len(), &program_id);
    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: register_ix(pk),
    };
    (
        mollusk.process_instruction(&ix, &[(acct_key, account)]),
        acct_key,
    )
}

#[test]
fn register_prepares_into_account_bit_exact() {
    let (r, acct_key) = run_register(PK);
    assert!(
        !r.program_result.is_err(),
        "on-chain prepare failed: {:?}",
        r.program_result
    );
    println!(
        "on-chain prepare (mode 2) OK — compute units consumed: {}",
        r.compute_units_consumed
    );
    // The decisive consensus check: bytes written on-chain must match the
    // host-prepared fixture exactly.
    let out = r
        .get_account(&acct_key)
        .expect("registered account present");
    assert_eq!(
        out.data.len(),
        PREPARED.len(),
        "registered account has the wrong length"
    );
    assert_eq!(
        &out.data[..],
        PREPARED,
        "on-chain prepare_into bytes differ from the host fixture"
    );
}

#[test]
fn register_rejects_invalid_pubkey() {
    // An all-zero wire pubkey is not a valid HAWK key (q00 not invertible);
    // `prepare_into` must return Err, surfaced as a program error.
    let (r, _) = run_register(&vec![0u8; PK.len()]);
    assert!(
        r.program_result.is_err(),
        "expected mode 2 to reject an invalid pubkey"
    );
}

#[test]
fn register_rejects_undersized_account() {
    let (mollusk, program_id) = make_mollusk();
    let acct_key = Address::new_unique();
    // One byte too small for the prepared blob.
    let account = Account::new(1_000_000_000, PREPARED.len() - 1, &program_id);
    let ix = Instruction {
        program_id,
        accounts: vec![AccountMeta::new(acct_key, false)],
        data: register_ix(PK),
    };
    let r = mollusk.process_instruction(&ix, &[(acct_key, account)]);
    assert!(
        r.program_result.is_err(),
        "expected mode 2 to reject an undersized account"
    );
}
