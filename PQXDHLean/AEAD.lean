/-
Authenticated Encryption with Associated Data (AEAD).

Definitions follow Bhargavan et al., USENIX Security 2024, §2.1.
Signal uses AES-256-CBC + HMAC in Encrypt-then-MAC mode.

## Current scope

This structure suffices for **correctness proofs** (X3DH_handshake_correct):
  - `encrypt` and `decrypt` are deterministic
  - Nonce is omitted — X3DH uses each session key exactly once

## Future work (security proofs)

When filling in the IND-CPA + INT-CTXT security proof (Theorem 2,
§3.2), two extensions may be needed:

  1. **Nonce parameter**: Real AEAD requires a nonce to avoid
     key-nonce reuse. The paper shows `enc(msg, 0, AD, SK)` where
     `0` is the nonce. For a general AEAD formalization, `encrypt`
     should become `K → PT → Nonce → AD → CT`.

  2. **Probabilistic encryption**: Some AEAD modes involve
     randomness (e.g., IV generation). Security proofs (IND-CPA)
     may require `encrypt` to be an `OracleComp unifSpec`.

The security assumption (IND-CPA + INT-CTXT) is formalized
separately in `SecurityDefs.lean` as an `opaque Prop`.
-/

/-- AEAD scheme parameterized by key `K`, plaintext `PT`, ciphertext `CT`,
and associated data `AD`. The `correctness` field guarantees that decrypting
an honestly encrypted ciphertext with the correct key and AD recovers the
original plaintext. -/
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt
