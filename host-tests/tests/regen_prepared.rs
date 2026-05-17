//! Fixture generator (not a real test — `#[ignore]`d so it only runs on
//! demand). Prepares the program's example pubkey once and writes the
//! crate-specific prepared blob so the Solana program can bake it in via
//! `include_bytes!` + the `const` `Hawk512PreparedPubkey::from_bytes`,
//! paying zero on-chain preparation cost.
//!
//! Regenerate (e.g. after changing the example keypair or the prepared
//! wire layout) with:
//!
//! ```sh
//! cargo test -p host-tests --test regen_prepared -- --ignored
//! ```

use solana_hawk512::{HAWK_512_PREPARED_PUBKEY_LEN, Hawk512Pubkey};

/// 8-byte-aligned scratch so `prepare_into`'s alignment guard passes
/// (mirrors on-chain account data, which Solana always 8-aligns).
#[repr(align(8))]
struct Aligned([u8; HAWK_512_PREPARED_PUBKEY_LEN]);

#[test]
#[ignore = "fixture generator; run explicitly with --ignored"]
fn regen_prepared_fixture() {
    const PK: &[u8] = include_bytes!("../../program/tests/fixtures/hawk.pk");
    let mut blob = Aligned([0u8; HAWK_512_PREPARED_PUBKEY_LEN]);
    Hawk512Pubkey::try_from(PK)
        .expect("example pubkey length")
        .prepare_into(&mut blob.0)
        .expect("example pubkey prepares");
    std::fs::write(
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../program/tests/fixtures/hawk.prepared"
        ),
        blob.0,
    )
    .expect("write prepared fixture");
}
