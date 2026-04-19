/-
Key Encapsulation Mechanism (KEM).

Definitions follow Bhargavan et al., USENIX Security 2024.
-/

/-- KEM parameterized by public key `PK`, secret key `SK_kem`,
ciphertext `CT`, and shared secret `SS`.

`matches pk sk` holds when `(pk, sk)` is a valid key pair produced by
honest key generation. This relation is required by `correctness` so
that the round-trip guarantee only applies to honestly generated pairs —
standard KEM correctness does not require decapsulation with an
arbitrary secret key to succeed. -/
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  /-- Valid key pairs, as produced by honest key generation. -/
  keyPairValid : PK → SK_kem → Prop
  /-- Standard KEM correctness: for any honestly generated key pair
  `(pk, sk)` satisfying `keyPairValid pk sk`, encapsulating under `pk` and
  then decapsulating under the matching `sk` recovers the shared secret. -/
  correctness : ∀ (pk : PK) (sk : SK_kem), keyPairValid pk sk →
    ∀ (ct : CT) (ss : SS), encaps pk = (ct, ss) → decaps sk ct = ss
