/-
Authenticated Encryption with Associated Data (AEAD).

Definitions follow Bhargavan et al., USENIX Security 2024.
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
