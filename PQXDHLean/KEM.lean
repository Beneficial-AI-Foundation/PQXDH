/-
Key Encapsulation Mechanism (KEM).

Definitions follow Bhargavan et al., USENIX Security 2024.
-/

/-- KEM parameterized by public key `PK`, secret key `SK_kem`,
ciphertext `CT`, and shared secret `SS`. The `correctness` field
guarantees that honest encapsulation/decapsulation round-trips. -/
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss
