/-
Abstract Key Encapsulation Mechanism (KEM).

A KEM provides a way for two parties to establish a shared secret
using public-key cryptography. One party encapsulates (producing a
ciphertext and a shared secret); the other decapsulates (recovering
the shared secret from the ciphertext using their private key).

In PQXDH, the KEM adds post-quantum secure entropy to the key
exchange. Blake publishes a KEM public key (PQSPK). Alex
encapsulates to get (ct, ss), appends ss to her KDF input, and
sends ct to Blake. Blake decapsulates to recover ss.

## Operations

  - `encaps`: given a public key, produce a ciphertext and shared secret
  - `decaps`: given a secret key and ciphertext, recover the shared secret
  - `correctness`: decapsulating an honestly generated ciphertext always
    recovers the same shared secret

## Security assumptions (§2.5, assumption 1.B)

The concrete instantiation is Kyber-1024 (ML-KEM), a lattice-based
KEM secure under the Module-LWE assumption. The paper assumes the
KEM is IND-CCA: an attacker who sees the public key and ciphertext
cannot distinguish the shared secret from a random value, even with
access to a decapsulation oracle for other ciphertexts.

## Note on randomness

In a real KEM, encapsulation is randomized — each call produces a
fresh (ct, ss) pair. We model encaps as a deterministic function
parameterized by the randomness, which is standard in formal
verification (the randomness is treated as an input rather than
being sampled internally).

Reference: Bhargavan et al., §2.3 and §2.5 assumption (1.B).
-/

/-! ## KEM structure -/

/-- Abstract Key Encapsulation Mechanism.

    Parameterized by:
    - `PK`: public key type
    - `SK_kem`: secret key type
    - `CT`: ciphertext type
    - `SS`: shared secret type

    Operations:
    - `encaps`: given a public key, produce a ciphertext and shared secret
    - `decaps`: given a secret key and ciphertext, recover the shared secret
    - `correctness`: honest encaps/decaps round-trips successfully -/

structure KEM (PK SK_kem CT SS : Type _) where
  /-- Encapsulate: produce a ciphertext and shared secret from a public key. -/
  encaps : PK → CT × SS
  /-- Decapsulate: recover the shared secret from a ciphertext using the secret key. -/
  decaps : SK_kem → CT → SS
  /-- Correctness: decapsulating an honestly encapsulated ciphertext
      recovers the same shared secret. -/
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss

/-! ## Correctness theorem -/

/-- KEM correctness: if encapsulation produces (ct, ss), then
    decapsulation with the corresponding secret key recovers ss. -/
theorem KEM_decaps_encaps {PK SK_kem CT SS : Type _} (kem : KEM PK SK_kem CT SS)
    (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS)
    (h : kem.encaps pk = (ct, ss)) :
    kem.decaps sk ct = ss :=
  kem.correctness pk sk ct ss h
