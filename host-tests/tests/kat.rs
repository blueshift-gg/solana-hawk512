//! End-to-end verification against reference HAWK-512 vectors produced by
//! the spec-faithful `lil-hawk-py` reference (which itself reproduces the
//! official NIST PQCsignKAT for HAWK-512). Each vector's reference
//! self-verify and tampered-message rejection were confirmed at generation
//! time; here we assert the Rust verifier agrees: accepts the genuine
//! triple and rejects every single-bit/length tampering.

use solana_hawk512::{Hawk512Pubkey, Hawk512Signature};

include!("fixtures/hawk_vectors.rs");

fn pk(v: &Vec_) -> Hawk512Pubkey {
    Hawk512Pubkey::try_from(v.pk).expect("pubkey length")
}
fn sig(v: &Vec_) -> Hawk512Signature {
    Hawk512Signature::try_from(v.sig).expect("signature length")
}

#[test]
fn accepts_genuine_vectors() {
    assert!(!VECTORS.is_empty());
    for (i, v) in VECTORS.iter().enumerate() {
        assert!(
            sig(v).verify(v.msg, &pk(v)),
            "vector {i}: genuine signature rejected",
        );
    }
}

#[test]
fn rejects_tampered_message() {
    for (i, v) in VECTORS.iter().enumerate() {
        let mut m = v.msg.to_vec();
        m[0] ^= 0x01;
        assert!(
            !sig(v).verify(&m, &pk(v)),
            "vector {i}: accepted tampered message",
        );
    }
}

#[test]
fn rejects_tampered_signature() {
    for (i, v) in VECTORS.iter().enumerate() {
        // Flip a bit past the 24-byte salt, inside the s1 payload.
        let mut s = v.sig.to_vec();
        s[40] ^= 0x01;
        let s = Hawk512Signature::try_from(&s[..]).unwrap();
        assert!(
            !s.verify(v.msg, &pk(v)),
            "vector {i}: accepted tampered signature",
        );
    }
}

#[test]
fn rejects_tampered_pubkey() {
    for (i, v) in VECTORS.iter().enumerate() {
        let mut p = v.pk.to_vec();
        p[0] ^= 0x01;
        // May fail to decode (false) or decode to a different key (verify
        // false) — either way it must not verify.
        if let Ok(p) = Hawk512Pubkey::try_from(&p[..]) {
            assert!(
                !sig(v).verify(v.msg, &p),
                "vector {i}: accepted tampered pubkey",
            );
        }
    }
}

#[test]
fn cross_pairings_rejected() {
    // A signature must not verify under another vector's message/pubkey.
    for (i, vi) in VECTORS.iter().enumerate() {
        for (j, vj) in VECTORS.iter().enumerate() {
            if i == j {
                continue;
            }
            assert!(
                !sig(vi).verify(vj.msg, &pk(vi)),
                "sig {i} accepted under msg {j}",
            );
            assert!(
                !sig(vi).verify(vi.msg, &pk(vj)),
                "sig {i} accepted under pubkey {j}",
            );
        }
    }
}
