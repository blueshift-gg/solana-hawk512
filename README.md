# Solana HAWK-512

> **DEPRECATED - do not use for anything that needs security.**
> HAWK was [withdrawn](https://hawk-sign.info/#withdrawal) from NIST's additional
> signatures standardisation process on 29 July 2026 after a key-recovery attack:
> [*HAWK-n Key Recovery Reduces to SVP in Dimension n/2 + 1*](https://eprint.iacr.org/2026/1593)
> (Straznickas & Weis, discovered with Claude 
> [write-up](https://www.anthropic.com/research/discovering-cryptographic-weaknesses))
> cuts HAWK-512 from 2^150 to 2^108 gates and HAWK-1024 from 2^288 to 2^182;
> HAWK-256 keys are recovered in hours on a single server. No parameter tweak
> saves the scheme. This repo is kept for reference only.

[![CI](https://github.com/blueshift-gg/solana-hawk512/actions/workflows/ci.yml/badge.svg)](https://github.com/blueshift-gg/solana-hawk512/actions/workflows/ci.yml)
[![Crates.io](https://img.shields.io/crates/v/solana-hawk512.svg)](https://crates.io/crates/solana-hawk512)
[![docs.rs](https://docs.rs/solana-hawk512/badge.svg)](https://docs.rs/solana-hawk512)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://github.com/blueshift-gg/solana-hawk512/blob/master/LICENSE)

A `no_std`, allocation-free, SVM-optimized **HAWK-512 post-quantum signature
verification** library (verify-only).

## Features

- **no_std, allocation-free**; only dependency is the shared
  [`solana-shake256`](https://crates.io/crates/solana-shake256) primitive.
- **Integer-only** — `RebuildS0`'s fixed-point FFT follows the spec
  step-for-step, so every verifier agrees bit-for-bit (on-chain consensus).
- **~365k CU** prepared / **~759k** raw, measured via Mollusk SVM
  (deterministic — no per-signature variance).
- **Zero-copy borrow APIs** (`from_ref`, `try_from_slice`): verify straight
  from instruction / account data, no memcpy.
- **Prepared-pubkey fast path**: an 18 464-byte blob of the pubkey-only
  FFT/NTT factors skips `DecodePublic`, `SHAKE256(pub)`, 2 FFTs and 4 NTTs
  per verify.
- Cross-checked against the official **NIST PQCsignKAT** vectors.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
solana-hawk512 = "0.1.0"
```

### Runtime pubkey

```rust
use solana_hawk512::{Hawk512Pubkey, Hawk512Signature};

let pubkey = Hawk512Pubkey::try_from(&pk_bytes[..])?;
let signature = Hawk512Signature::try_from(&sig_bytes[..])?;
let ok = signature.verify(message, &pubkey);
```

### Compile-time prepared pubkey (recommended for Solana programs)

Bake a fixed pubkey's prepared blob into `.rodata` (8-byte-aligned) and
borrow it **zero-copy** — zero on-chain preparation cost, nothing on the
stack:

```rust
use solana_hawk512::{HAWK_512_PREPARED_PUBKEY_LEN, Hawk512PreparedPubkey, Hawk512Signature};

#[repr(C, align(8))]
struct Aligned([u8; HAWK_512_PREPARED_PUBKEY_LEN]);
static PREPARED_BYTES: Aligned = Aligned(*include_bytes!("../keys/hawk.prepared"));

// SAFETY: `#[repr(C, align(8))]` ⇒ `.0` is 8-aligned, as `from_ref` requires.
let prepared = unsafe { Hawk512PreparedPubkey::from_ref(&PREPARED_BYTES.0) };
let ok = signature.verify_with_prepared(message, prepared);
```

(`from_bytes` returns the blob *by value* — fine in a `const`/host context,
but never call it at SBF runtime: 18 KiB exceeds the 4 KiB SBF frame. Borrow
in place instead, as above.) Produce the blob with `prepare_into` +
`as_bytes` (see [Regenerating the prepared blob](#regenerating-the-prepared-blob)).

### Runtime prepared pubkey (multi-tenant programs)

For per-account/per-user keys not known at compile time, store the
**prepared** form in account data. `prepare_into` runs the preparation
**on-chain at registration**, writing straight into the account:

```rust
use solana_hawk512::{
    HAWK_512_PREPARED_PUBKEY_LEN, Hawk512PreparedPubkey, Hawk512Pubkey, Hawk512Signature,
};

// Registration (on-chain): decode the wire pubkey and write the
// 18 464-byte prepared form straight into the program-owned account.
// Nothing 18 KiB ever lands on the stack — the result is the account.
let pk = Hawk512Pubkey::try_from(&pk_wire_bytes[..])?;
let out: &mut [u8; HAWK_512_PREPARED_PUBKEY_LEN] =
    (&mut account_data[..HAWK_512_PREPARED_PUBKEY_LEN]).try_into()?;
pk.prepare_into(out)?;

// Verify (every later call): borrow the prepared pubkey directly out of
// (8-byte-aligned) account data — no copy, no allocation.
let prepared = unsafe { Hawk512PreparedPubkey::try_from_slice(&account_data[..])? };
let signature = Hawk512Signature::try_from_slice(sig_bytes)?;
let ok = signature.verify_with_prepared(message, prepared);
```

`prepare_into` returns `Err(InvalidArgument)` on a malformed pubkey, a
non-invertible `q00`, or a misaligned `out`. It runs on-chain: the
transient working set is split across `#[inline(never)]` frames ≤ 4 KiB and
the 18 KiB result is written in place into the account, never on the stack.

## Compatibility

| Variant                                | Supported |
| -------------------------------------- | --------- |
| HAWK-512 (NIST level 1)                | ✅        |
| HAWK-256 / HAWK-1024                    | ❌        |
| Sign / keygen                          | ❌ (verify only — generate keys with the HAWK reference implementation) |

HAWK v1.0 and v1.1 are **algorithmically identical** (the v1.0→v1.1 change
touched only the security proofs / BUFF / omSVP analysis, not the algorithms
or wire formats), so v1.0 KAT vectors apply unchanged.

### Prepared pubkey: a blockchain-specific optimisation

A standard HAWK verifier sees each pubkey once. On-chain the same pubkey is
verified many times and storage is rent-paid, so it pays to precompute the
pubkey-only work once and skip it per verify. `Hawk512PreparedPubkey` bakes
in: `DecodePublic` (Golomb–Rice unpack of `q00`/`q01`); `hpub =
SHAKE256(pub)`; the `RebuildS0` pubkey FFT `q̂01` plus the divide-loop bound
`(1≪32)·(α+q̂00)` (validated at prepare); and the two per-prime `PolyQnorm`
NTTs (`q̂00`, `q̂01`) with the `q̂00⁻¹` batch inversion — leaving only the
signature-dependent FFT/NTTs on-chain.

The 18 464-byte wire format is **specific to this crate** (not interoperable
— the 1024-byte standard wire pubkey is the interoperability boundary). Rent
amortises over many verifications.

## Benchmarks

Measured via Mollusk SVM (default optimised build):

| Path                                 | CUs   |
| ------------------------------------ | ----- |
| `verify_with_prepared`               | ~365k |
| `verify` (raw 1024-byte wire pubkey) | ~759k |
| `prepare_into` (one-time, on-chain)  | ~416k |

Cost is fixed (no per-signature variance). A safe prepared-path budget is
`set_compute_unit_limit(385_000)`; both verify paths sit well under Solana's
1.4M cap, but the prepared path is preferred (~half the cost, and it dodges
the 1232-byte tx limit).

### Optimisation journey

`verify` started as a faithful ~2M-CU spec port. Milestones:

| Stage                                                            | `verify` | `prepared` |
| ---------------------------------------------------------------- | -------- | ---------- |
| Naive integer spec port                                          | ~2,000k  | —          |
| Frame-split stack arena + iterator bounds-check elision          | ~1,460k  | —          |
| Lane-complementing Keccak; native `% p` (beats Montgomery)       | ~1,390k  | —          |
| **Prepared pubkey** (skip decode, `SHAKE256(pub)`, 2 FFT, 4 NTT) | 1,390k   | **758k**   |
| `i64::div_euclid` → unsigned divide / arithmetic shift           | 1,212k   | 579k       |
| Golomb–Rice low-bits: 2-byte word read instead of per-bit        | 1,068k   | 536k       |
| Lazy ê / deferred ĉ-sum; precomputed divide bounds               | 1,039k   | 510k       |
| **Macro loop-unroll** (each NTT/FFT level size as a `const`)     | 887k     | 435k       |
| Bounded NTT lazy-reduction (defer additive `% p`)                | 862k     | 422k       |
| Const-generic `decompress_gr` / `squeeze`                        | 841k     | 411k       |
| Pass-fusion (conversion folded into transform first/last level)  | 788k     | 380k       |
| `i64` FFT-domain storage (no SBPF-v1 per-load sign-extension)    | 765k     | 367k       |
| Golomb sign: `x ^ -s` instead of `x − s·(2x+1)`                  | **759k** | **365k**   |

Findings, all **measured** on SBF and counter to CPU intuition:

- **64-bit `a % p` is one cheap native op.** Conditional subtraction is ~8%
  *slower*; u128 Barrett and Shoup ~80k slower (no hardware multiply-high).
- **Signed `i64::div_euclid` is a software routine.** RebuildS0's two
  floor-divides become an unsigned divide and an arithmetic shift — ~180k.
- **The lever is killing the *runtime* loop bound, not the loop shape.**
  Const block sizes (macro, ~150k) + const generics (~20k) let LLVM fold
  bounds/masks and unroll; iterator vs hand-unrolled was byte-identical.
- **Pass-fusion**: fold each pre/post conversion pass into the transform's
  first/last level — one fewer N-pass + 2 KiB temp each, bit-identical.
- **Bounded NTT lazy-reduction**: `2p < 2³²`, so defer the additive `% p`
  on alternate levels (values stay `< 2³²`), reduce by level 9 —
  bit-identical to reducing every level; the static schedule keeps it sound.
- **`i64` FFT domain**: SBPF-v1 has no sign-extending load; an op-count
  argument said `i64` was neutral but it measured **~13% faster** (store-
  side truncation schedules better than a per-load `lsh;arsh` chain).

## Project layout

- `src/` — verify library (`no_std`, rlib). Only dependency:
  [`solana-shake256`](https://crates.io/crates/solana-shake256) (shared
  SHAKE256/Keccak primitive, also used by
  [`solana-falcon512`](https://github.com/blueshift-gg/solana-falcon512)).
- `host-tests/` — integration tests (KAT e2e, prepared round-trip, fixture
  generator) in a separate crate so the main crate stays lean.
- `program/` — minimal Solana program (raw / baked-in prepared / on-chain
  register), with Mollusk SBF tests measuring each path's compute cost.

## Testing

```sh
cargo test --workspace                          # lib unit + KAT e2e + prepared round-trip
(cd program && cargo build-sbf \
   && SBF_OUT_DIR=../target/deploy cargo test --test tests -- --nocapture)  # SBF + CU
```

`prepared.rs` confirms `verify_with_prepared` agrees bit-for-bit with
`verify`, rejects all tampering, and round-trips the wire format; the
Mollusk suite additionally checks the on-chain `prepare_into` output is
byte-identical to the host fixture.

### Regenerating the prepared blob

`program/tests/fixtures/hawk.prepared` is the example pubkey in prepared
form, baked into the program via `include_bytes!`. Regenerate it (after
changing the example keypair or the wire layout) with:

```sh
cargo test -p host-tests --test regen_prepared -- --ignored
```

## Security

Verification operates exclusively on public data (signature, pubkey,
message), so the implementation is deliberately **not** constant-time — it
short-circuits on decode / `sym-break` / fixed-point-range /
dual-prime-mismatch / norm-bound failures. None of those leak secret
information.

For the underlying cryptography see [HAWK](https://hawk-sign.info).

### Common footguns

1. **Wire-format validity ≠ a valid pubkey.** Decoding only checks the wire
   format; any parsing 1024-byte buffer is accepted. Bind keys to identities
   with a registration challenge if that matters.
2. **No built-in domain separation.** `M ← SHAKE256(message ‖ hpub)` has no
   protocol prefix; add your own if a keypair is reused across protocols.
3. **Transaction size.** A raw verify needs 1024-byte pubkey + 555-byte
   signature, over Solana's 1232-byte legacy limit. Store a prepared pubkey
   in an account so only the 555-byte signature travels in the instruction.
4. **Prepared-pubkey alignment.** `from_ref` / `try_from_slice` require
   **8-byte alignment**. Account/instruction data is 8-aligned; an arbitrary
   `Vec<u8>` offset may not be — use `from_bytes` (copies) if unsure.
5. **Security level.** NIST PQC level 1 (~128-bit classical / ~120-bit
   post-quantum). Rotate keys periodically.

## Status

**Not audited.** Cross-checked against the official NIST PQCsignKAT
HAWK-512 vectors (via the spec-faithful `lil-hawk-py` reference): every
genuine triple verifies, and every single-bit / length / cross-pairing
tampering is rejected, on both the raw and prepared paths.

## Disclaimer

Provided strictly "AS IS", without warranty of any kind — including
correctness, security, or fitness for a particular purpose. The authors
accept no liability for any loss or damage. Audit it and test it against
your own threat model before deploying.

## License

[MIT](https://github.com/blueshift-gg/solana-hawk512/blob/master/LICENSE).
