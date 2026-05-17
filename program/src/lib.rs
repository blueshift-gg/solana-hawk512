#![cfg_attr(any(target_arch = "bpf", target_os = "solana"), no_std)]

//! Minimal Solana program demonstrating in-program HAWK-512 verification
//! and on-chain pubkey registration.
//!
//! Instruction data is `[mode: 1 byte][payload]`:
//!
//! - `mode = 0` — raw pubkey, zero accounts:
//!   `payload = [pubkey: 1024][signature: 555][message]`. Decodes the wire
//!   pubkey on every call (the interoperability path).
//! - `mode = 1` — compile-time prepared pubkey, zero accounts:
//!   `payload = [signature: 555][message]`, verified against
//!   [`PREPARED_BYTES`] (an 8-aligned blob baked into `.rodata`), borrowed
//!   zero-copy via [`Hawk512PreparedPubkey::from_ref`]. The fixed-signer
//!   shortcut: the ~18 KiB of pubkey-only FFT/NTT factors live in `.rodata`,
//!   so only the 555-byte signature + message travel in the transaction
//!   (well under Solana's 1232-byte legacy limit, unlike a raw 1024-byte
//!   pubkey).
//! - `mode = 2` — **registration**, one writable program-owned account:
//!   `payload = [pubkey: 1024]`. Runs [`Hawk512Pubkey::prepare_into`]
//!   on-chain and writes the [`HAWK_512_PREPARED_PUBKEY_LEN`]-byte prepared
//!   form straight into the account. This is the general path for
//!   arbitrary, runtime-supplied keys: prepare once here, then every later
//!   `mode = 1`-style verify reads the prepared blob back out of the
//!   account. The ~18 KiB result lives in the account, never on the stack.

use solana_hawk512::{
    HAWK_512_PREPARED_PUBKEY_LEN, HAWK_512_PUBKEY_LEN, HAWK_512_SIGNATURE_LEN,
    Hawk512PreparedPubkey, Hawk512Pubkey, Hawk512Signature,
};
use solana_program_error::ProgramError;

#[cfg(any(target_arch = "bpf", target_os = "solana"))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}

// No allocator: `solana-hawk512` keeps its entire transient working set on
// the stack (split across `#[inline(never)]` call frames, each ≤ 4 KiB),
// and `prepare_into` writes its 18 KiB result into the caller's account, so
// this program needs neither a heap nor any writable globals.

/// 8-byte-aligned wrapper so the baked blob can be borrowed zero-copy via
/// [`Hawk512PreparedPubkey::from_ref`] (which requires 8-byte alignment).
#[repr(C, align(8))]
struct AlignedPrepared([u8; HAWK_512_PREPARED_PUBKEY_LEN]);

/// The example pubkey for the fixed-signer shortcut (`mode = 1`), prepared
/// ahead of time and baked into `.rodata`. It is borrowed **zero-copy** at
/// use (see `mode = 1`): the ~18 KiB never lands on the stack, and the
/// large by-value `from_bytes` constructor is never referenced from SBF.
/// (`mode = 2` shows the general case: preparing an arbitrary key on-chain
/// into an account.) Regenerate the blob with
/// `cargo test -p host-tests --test regen_prepared -- --ignored`.
static PREPARED_BYTES: AlignedPrepared =
    AlignedPrepared(*include_bytes!("../tests/fixtures/hawk.prepared"));

const ERR_VERIFY_FAILED: u64 = 3;
const ERR_PREPARE_FAILED: u64 = 4;

/// `MAX_PERMITTED_DATA_INCREASE` — the realloc-headroom region the runtime
/// reserves after each account's data in the serialized input.
const MAX_PERMITTED_DATA_INCREASE: usize = 10 * 1024;
/// First byte of an account record: `0xFF` ⇒ not a duplicate of an earlier
/// account (`solana_program_entrypoint::NON_DUP_MARKER`).
const NON_DUP_MARKER: u8 = 0xff;

/// Solana SBF entrypoint. The serialized input is
/// `[u64 num_accounts][account…][u64 ix_data_len][ix_data][program_id]`.
/// This demo accepts 0 accounts (`mode = 0`/`1`) or exactly 1 writable
/// program-owned account (`mode = 2`); the account block is walked to
/// locate the instruction data, mirroring `solana_program_entrypoint`'s
/// deserialize for the standard (aligned) loader.
///
/// # Safety
///
/// The Solana runtime guarantees `input` points to a properly-laid-out,
/// aligned region serialized exactly as above.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
    // [0,8): u64 num_accounts. Then `off` walks the account block.
    let num_accounts = unsafe { core::ptr::read(input as *const u64) } as usize;
    let mut off = 8usize;
    // For `mode = 2`: the single account's data pointer + length.
    let mut acct: Option<(*mut u8, usize)> = None;

    if num_accounts == 1 {
        // Account record (non-duplicate, aligned loader):
        //   +0 dup(1) signer(1) writable(1) exec(1) orig_data_len(4)
        //   +8 key(32) owner(32) lamports(8) data_len(8) data(data_len)
        // then MAX_PERMITTED_DATA_INCREASE + rent_epoch(8) + align-to-8 pad.
        if unsafe { core::ptr::read(input.add(off)) } != NON_DUP_MARKER {
            return ProgramError::InvalidInstructionData.into(); // no dup support
        }
        // Header (dup..data_len) = 1+1+1+1+4+32+32+8+8 = 88 bytes: data_len
        // is the last u64 of the header (at off+80), data starts at off+88.
        let data_len =
            unsafe { core::ptr::read_unaligned(input.add(off + 80) as *const u64) } as usize;
        let data_ptr = unsafe { input.add(off + 88) };
        acct = Some((data_ptr, data_len));
        off += 88 + data_len + MAX_PERMITTED_DATA_INCREASE + 8 /* rent_epoch */;
        off += (off as *const u8).align_offset(8); // serializer padding
    } else if num_accounts != 0 {
        return ProgramError::InvalidInstructionData.into();
    }

    // [off,off+8): u64 ix_data_len, then the instruction data.
    let ix_data_len = unsafe { core::ptr::read_unaligned(input.add(off) as *const u64) } as usize;
    if ix_data_len < 1 {
        return ProgramError::InvalidInstructionData.into();
    }
    let data = unsafe { core::slice::from_raw_parts(input.add(off + 8), ix_data_len) };
    let (&mode, payload) = data.split_first().unwrap();

    let ok = match mode {
        // Raw pubkey: [pubkey][signature][message].
        0 => {
            let Some((pk_bytes, rest)) = payload.split_first_chunk::<HAWK_512_PUBKEY_LEN>() else {
                return ProgramError::InvalidInstructionData.into();
            };
            let Some((sig_bytes, message)) = rest.split_first_chunk::<HAWK_512_SIGNATURE_LEN>()
            else {
                return ProgramError::InvalidInstructionData.into();
            };
            Hawk512Signature::from_ref(sig_bytes).verify(message, Hawk512Pubkey::from_ref(pk_bytes))
        }
        // Prepared (baked-in) pubkey: [signature][message].
        1 => {
            let Some((sig_bytes, message)) = payload.split_first_chunk::<HAWK_512_SIGNATURE_LEN>()
            else {
                return ProgramError::InvalidInstructionData.into();
            };
            // SAFETY: `PREPARED_BYTES` is `#[repr(C, align(8))]`, so `.0` is
            // 8-aligned as `from_ref` requires; trusted crate fixture bytes.
            let prepared = unsafe { Hawk512PreparedPubkey::from_ref(&PREPARED_BYTES.0) };
            Hawk512Signature::from_ref(sig_bytes).verify_with_prepared(message, prepared)
        }
        // Registration: [pubkey] → prepare on-chain straight into the
        // account's data (the 18 KiB result never touches the stack).
        2 => {
            let Some((data_ptr, data_len)) = acct else {
                return ProgramError::InvalidInstructionData.into(); // account required
            };
            if data_len < HAWK_512_PREPARED_PUBKEY_LEN {
                return ProgramError::AccountDataTooSmall.into();
            }
            let Some((pk_bytes, _)) = payload.split_first_chunk::<HAWK_512_PUBKEY_LEN>() else {
                return ProgramError::InvalidInstructionData.into();
            };
            // SAFETY: account data is writable, ≥ LEN bytes, and 8-aligned
            // (the runtime serializes account data on an 8-byte boundary);
            // `prepare_into` re-checks the alignment and fully writes it.
            let out = unsafe { &mut *(data_ptr as *mut [u8; HAWK_512_PREPARED_PUBKEY_LEN]) };
            return match Hawk512Pubkey::from_ref(pk_bytes).prepare_into(out) {
                Ok(()) => 0,
                Err(_) => ERR_PREPARE_FAILED,
            };
        }
        _ => return ProgramError::InvalidInstructionData.into(),
    };

    if ok { 0 } else { ERR_VERIFY_FAILED }
}
