//! `Hawk512PreparedPubkey` end-to-end: preparing a pubkey, serialising it
//! (`as_bytes`), deserialising it (`from_bytes`), and confirming
//! `verify_with_prepared` agrees bit-for-bit with the direct `verify` path —
//! accepts every genuine vector, rejects tampering, and round-trips the
//! crate-specific wire format.

use solana_hawk512::{
    HAWK_512_PREPARED_PUBKEY_LEN, Hawk512PreparedPubkey, Hawk512Pubkey, Hawk512Signature,
};

include!("fixtures/hawk_vectors.rs");

fn pk(v: &Vec_) -> Hawk512Pubkey {
    Hawk512Pubkey::try_from(v.pk).expect("pubkey length")
}
fn sig(v: &Vec_) -> Hawk512Signature {
    Hawk512Signature::try_from(v.sig).expect("signature length")
}

/// 8-byte-aligned scratch so `prepare_into`'s alignment guard passes (Solana
/// account data is always 8-aligned; here we model that off-chain).
#[repr(align(8))]
struct Aligned([u8; HAWK_512_PREPARED_PUBKEY_LEN]);

/// Run the on-chain `prepare_into` path into an aligned buffer and return an
/// owned prepared pubkey (mirrors registration: prepare once, store bytes).
fn prepare(p: &Hawk512Pubkey) -> Hawk512PreparedPubkey {
    let mut blob = Aligned([0u8; HAWK_512_PREPARED_PUBKEY_LEN]);
    p.prepare_into(&mut blob.0).expect("prepare");
    Hawk512PreparedPubkey::from_bytes(blob.0)
}

#[test]
fn prepared_accepts_genuine_and_matches_direct() {
    assert!(!VECTORS.is_empty());
    for (i, v) in VECTORS.iter().enumerate() {
        let prepared = prepare(&pk(v));
        assert!(
            sig(v).verify_with_prepared(v.msg, &prepared),
            "vector {i}: prepared verify rejected a genuine signature",
        );
        // Same verdict as the raw-pubkey path.
        assert_eq!(
            sig(v).verify(v.msg, &pk(v)),
            sig(v).verify_with_prepared(v.msg, &prepared),
            "vector {i}: prepared/direct disagree (genuine)",
        );
    }
}

#[test]
fn prepared_serialisation_roundtrips() {
    for (i, v) in VECTORS.iter().enumerate() {
        let prepared = prepare(&pk(v));
        let bytes: [u8; HAWK_512_PREPARED_PUBKEY_LEN] = *prepared.as_bytes();
        // const-fn decode path (the `include_bytes!` / compile-time form).
        let restored = Hawk512PreparedPubkey::from_bytes(bytes);
        assert_eq!(
            restored.as_bytes(),
            prepared.as_bytes(),
            "vector {i}: from_bytes∘as_bytes is not identity",
        );
        assert!(
            sig(v).verify_with_prepared(v.msg, &restored),
            "vector {i}: round-tripped prepared pubkey failed to verify",
        );
        // Zero-copy borrow path (the blob is 8-aligned inside the array).
        let borrowed = unsafe { Hawk512PreparedPubkey::from_ref(&bytes) };
        assert!(
            sig(v).verify_with_prepared(v.msg, borrowed),
            "vector {i}: from_ref prepared pubkey failed to verify",
        );
    }
}

#[test]
fn prepared_rejects_tampering() {
    for (i, v) in VECTORS.iter().enumerate() {
        let prepared = prepare(&pk(v));

        // Tampered message.
        let mut m = v.msg.to_vec();
        m[0] ^= 0x01;
        assert!(
            !sig(v).verify_with_prepared(&m, &prepared),
            "vector {i}: prepared accepted a tampered message",
        );

        // Tampered signature (past the 24-byte salt, inside s1).
        let mut s = v.sig.to_vec();
        s[40] ^= 0x01;
        let s = Hawk512Signature::try_from(&s[..]).unwrap();
        assert!(
            !s.verify_with_prepared(v.msg, &prepared),
            "vector {i}: prepared accepted a tampered signature",
        );

        // A prepared pubkey from a different key must reject this signature.
        let other = &VECTORS[(i + 1) % VECTORS.len()];
        if other.pk != v.pk {
            let other_prepared = prepare(&pk(other));
            assert!(
                !sig(v).verify_with_prepared(v.msg, &other_prepared),
                "vector {i}: verified under a different prepared pubkey",
            );
        }
    }
}
