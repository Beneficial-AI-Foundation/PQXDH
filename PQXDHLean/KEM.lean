/-
Key Encapsulation Mechanism (KEM).

Definitions follow Bhargavan et al., USENIX Security 2024, §2.1.

## Current scope

This structure suffices for **correctness proofs** (PQXDH_agree):
  - `encaps` and `decaps` are deterministic
  - `keygen` is omitted — callers supply matching (pk, sk) pairs

## Future work (security proofs)

When filling in the IND-CCA security proof (Theorem 3, §3.2) or
the SH-CR proof (Theorem 5, §4), two extensions are needed:

  1. **`keygen`**: The IND-CCA game begins with `(pk, sk) ← KEM.keygen`.
     This should be a probabilistic operation (`OracleComp unifSpec`).

  2. **Probabilistic `encaps`**: Real KEM encapsulation is randomized.
     For security proofs, `encaps` should become
     `PK → OracleComp unifSpec (CT × SS)`, similar to how `KDF` has
     a deterministic form (`KDF.derive`) and a probabilistic form
     (`KDFOracle` as a random oracle).

  One approach: introduce a separate `KEMSpec` (probabilistic, for
  security) alongside this `KEM` (deterministic, for correctness).
-/

/-- KEM parameterized by public key `PK`, secret key `SK_kem`,
ciphertext `CT`, and shared secret `SS`. The `correctness` field
guarantees that honest encapsulation/decapsulation round-trips. -/
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss
