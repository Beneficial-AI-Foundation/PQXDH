/-
Example: X3DH protocol run over ℤ (the integers).

We instantiate the abstract X3DH formalization with:
  - Group G = ℤ (integers under addition)
  - Generator G₀ = 1
  - DH(a, B) = a • B = a * B (scalar multiplication = ordinary multiplication)
  - KDF: identity function (the DH tuple *is* the session key)
  - AEAD: additive toy scheme (encrypt = plaintext + key, decrypt = ciphertext - key)

This is NOT cryptographically secure — it is a concrete worked example
showing how the abstract theorems compose into a complete protocol run.

Why this example is insecure:

  1. The group ℤ has no discrete log hardness. In a real protocol, given
     the public key IKₐ = [ikₐ]G on an elliptic curve, you can't recover
     the private scalar ikₐ. In ℤ, DH(3, 1) = 3 — the "private key" is
     the public key. Anyone can read it.

  2. The KDF is the identity function. A real KDF (HKDF-SHA256) is a
     one-way function: given the output, you can't recover the input.
     Our toyKDF just passes the DH tuple through unchanged, so the
     session key leaks all DH values.

  3. The AEAD is just addition. A real AEAD (AES-256-CBC + HMAC) produces
     ciphertexts that are indistinguishable from random. Our toyAEAD
     computes ct = pt + k₁ + k₂ + k₃ + k₄ — if you know any two of
     {plaintext, key, ciphertext}, you can recover the third. There is
     no real confidentiality or integrity.

The example only demonstrates that the abstract theorems compose
correctly — that the types line up and the proof goes through. The
security of X3DH comes from the cryptographic assumptions on these
primitives (GapDH, random oracle KDF, IND-CPA+INT-CTXT AEAD), not
from the algebraic structure alone.

## Concrete key values

  Alice's identity key:    ikₐ  = 3,   IKₐ  = 3 * 1 = 3
  Alice's ephemeral key:   ekₐ  = 5,   EKₐ  = 5 * 1 = 5
  Bob's identity key:      ikᵦ  = 7,   IKᵦ  = 7 * 1 = 7
  Bob's signed prekey:     spkᵦ = 11,  SPKᵦ = 11 * 1 = 11
  Bob's one-time prekey:   opkᵦ = 13,  OPKᵦ = 13 * 1 = 13

## DH computations

  Alice computes:
    DH1 = DH(ikₐ,  SPKᵦ) = 3  * 11 = 33
    DH2 = DH(ekₐ,  IKᵦ)  = 5  * 7  = 35
    DH3 = DH(ekₐ,  SPKᵦ) = 5  * 11 = 55
    DH4 = DH(ekₐ,  OPKᵦ) = 5  * 13 = 65

  Bob computes:
    DH1 = DH(spkᵦ, IKₐ)  = 11 * 3  = 33  ✓
    DH2 = DH(ikᵦ,  EKₐ)  = 7  * 5  = 35  ✓
    DH3 = DH(spkᵦ, EKₐ)  = 11 * 5  = 55  ✓
    DH4 = DH(opkᵦ, EKₐ)  = 13 * 5  = 65  ✓

  Both get the tuple (33, 35, 55, 65), so SK_A = SK_B.
-/
import PQXDHLean.X3DH
import Mathlib.Tactic.Ring

/-! ## Toy KDF: identity function

The simplest possible KDF — the DH tuple is used directly as the
session key. In a real protocol this would be HKDF-SHA256. -/

/-- Toy KDF that returns its input unchanged. -/
def toyKDF : KDF (ℤ × ℤ × ℤ × ℤ) (ℤ × ℤ × ℤ × ℤ) where
  derive := id

/-! ## Toy AEAD: additive cipher

Encrypts by adding the key components to the plaintext;
decrypts by subtracting. Associated data is stored alongside the
ciphertext and checked on decryption (modelling authentication).
This is trivially correct but obviously not secure — it serves only
to demonstrate the composition of KDF + AEAD in the handshake theorem. -/

/-- Toy AEAD over ℤ.
    - Key:        (ℤ × ℤ × ℤ × ℤ)  (the session key / DH tuple)
    - Plaintext:  ℤ                  (a single integer message)
    - Ciphertext: ℤ × (ℤ × ℤ)       (encrypted value, copy of AD for auth check)
    - Assoc data: ℤ × ℤ              (the two identity public keys) -/
def toyAEAD : AEAD (ℤ × ℤ × ℤ × ℤ) ℤ (ℤ × (ℤ × ℤ)) (ℤ × ℤ) where
  encrypt := fun ⟨k₁, k₂, k₃, k₄⟩ pt ad =>
    (pt + k₁ + k₂ + k₃ + k₄, ad)
  decrypt := fun ⟨k₁, k₂, k₃, k₄⟩ ⟨c, ad'⟩ ad =>
    if ad' = ad then some (c - k₁ - k₂ - k₃ - k₄) else none
  correctness := by
    intro ⟨k₁, k₂, k₃, k₄⟩ pt ⟨a₁, a₂⟩
    change (if (a₁, a₂) = (a₁, a₂) then some _ else none) = some pt
    rw [if_pos rfl]
    congr 1
    ring

/-! ## Concrete key values -/

/-- Generator: 1 ∈ ℤ -/
def G₀ : ℤ := 1

-- Alice's keys
def alice_ik : ℕ := 3 -- identity key (private)
def alice_ek : ℕ := 5 -- ephemeral key (private)

-- Bob's keys
def bob_ik : ℕ := 7 -- identity key (private)
def bob_spk : ℕ := 11 -- signed prekey (private)
def bob_opk : ℕ := 13 -- one-time prekey (private)

-- Public keys: [scalar]G₀
noncomputable def IKₐ : ℤ := DH alice_ik G₀
noncomputable def EKₐ : ℤ := DH alice_ek G₀
noncomputable def IKᵦ : ℤ := DH bob_ik G₀
noncomputable def SPKᵦ : ℤ := DH bob_spk G₀
noncomputable def OPKᵦ : ℤ := DH bob_opk G₀

/-! ## Protocol run

We now apply the handshake correctness theorem to our concrete values.
This proves that Bob can decrypt Alice's first message. -/

/-- Alice's message: the integer 42 ("hello"). -/
def alice_msg : ℤ := 42

/-- Alice encrypts her message with her session key and AD = (IKₐ, IKᵦ). -/
noncomputable def alice_ciphertext : ℤ × (ℤ × ℤ) :=
  toyAEAD.encrypt
    (X3DH_SK_Alice toyKDF alice_ik alice_ek IKᵦ SPKᵦ OPKᵦ)
    alice_msg
    (IKₐ, IKᵦ)

/-- End-to-end correctness: Bob decrypts Alice's ciphertext and recovers
    the original message 42.

    This is a direct application of `X3DH_handshake_correct` with:
    - G = ℤ, G₀ = 1
    - toyKDF as the key derivation function
    - toyAEAD as the authenticated encryption scheme
    - concrete private keys (3, 5, 7, 11, 13)
    - AD = (IKₐ, IKᵦ) = (3, 7) -/
theorem bob_decrypts_alice :
    toyAEAD.decrypt
      (X3DH_SK_Bob toyKDF bob_ik bob_spk bob_opk IKₐ EKₐ)
      alice_ciphertext
      (IKₐ, IKᵦ) = some alice_msg :=
  X3DH_handshake_correct
    toyKDF toyAEAD G₀
    alice_ik alice_ek bob_ik bob_spk bob_opk
    rfl rfl rfl rfl rfl
    alice_msg alice_ciphertext rfl
