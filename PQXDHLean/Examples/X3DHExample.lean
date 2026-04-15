/-
Example: X3DH protocol run over ℚ (the rationals).

We instantiate the abstract X3DH formalization with:
  - Scalar field F = ℚ
  - Group G = ℚ (rationals under addition, with Module ℚ ℚ = scalar multiplication)
  - Generator G₀ = 1
  - DH(a, B) = a • B = a * B (field-scalar multiplication = ordinary multiplication)
  - KDF: identity function (the DH tuple *is* the session key)
  - AEAD: additive toy scheme (encrypt = plaintext + key, decrypt = ciphertext - key)

This is NOT cryptographically secure — it is a concrete worked example
showing how the abstract theorems compose into a complete protocol run.

## Concrete key values

  Alice's identity key:    ikₐ  = 3,   IKₐ  = DH(3, 1)  = 3
  Alice's ephemeral key:   ekₐ  = 5,   EKₐ  = DH(5, 1)  = 5
  Bob's identity key:      ikᵦ  = 7,   IKᵦ  = DH(7, 1)  = 7
  Bob's signed prekey:     spkᵦ = 11,  SPKᵦ = DH(11, 1) = 11
  Bob's one-time prekey:   opkᵦ = 13,  OPKᵦ = DH(13, 1) = 13

## DH computations

  Alice computes:
    DH1 = DH(ikₐ,  SPKᵦ) = DH(3,  11) = 33
    DH2 = DH(ekₐ,  IKᵦ)  = DH(5,  7)  = 35
    DH3 = DH(ekₐ,  SPKᵦ) = DH(5,  11) = 55
    DH4 = DH(ekₐ,  OPKᵦ) = DH(5,  13) = 65

  Bob computes:
    DH1 = DH(spkᵦ, IKₐ)  = DH(11, 3)  = 33  ✓
    DH2 = DH(ikᵦ,  EKₐ)  = DH(7,  5)  = 35  ✓
    DH3 = DH(spkᵦ, EKₐ)  = DH(11, 5)  = 55  ✓
    DH4 = DH(opkᵦ, EKₐ)  = DH(13, 5)  = 65  ✓

  Both get the tuple (33, 35, 55, 65), so SKₐ = SK_B.
-/
import PQXDHLean.X3DH.X3DH
import Mathlib.Tactic.Ring

/-! ## Toy KDF: identity function -/

/-- Toy KDF that returns its input unchanged. -/
def toyKDF : KDF (ℚ × ℚ × ℚ × ℚ) (ℚ × ℚ × ℚ × ℚ) where
  derive := id

/-! ## Toy AEAD: additive cipher -/

/-- Toy AEAD over ℚ. Encrypts by adding key components; decrypts by subtracting.
Associated data is stored alongside ciphertext and checked on decryption. -/
def toyAEAD : AEAD (ℚ × ℚ × ℚ × ℚ) ℚ (ℚ × (ℚ × ℚ)) (ℚ × ℚ) where
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

def G₀ : ℚ := 1

-- Key pairs: KeyPair ℚ ℚ G₀
def alice_IK : KeyPair ℚ ℚ G₀ := ⟨3, DH 3 G₀, rfl⟩
def alice_EK : KeyPair ℚ ℚ G₀ := ⟨5, DH 5 G₀, rfl⟩
def bob_IK : KeyPair ℚ ℚ G₀ := ⟨7, DH 7 G₀, rfl⟩
def bob_SPK : KeyPair ℚ ℚ G₀ := ⟨11, DH 11 G₀, rfl⟩
def bob_OPK : KeyPair ℚ ℚ G₀ := ⟨13, DH 13 G₀, rfl⟩

/-! ## Protocol run -/

def alice_msg : ℚ := 42

def alice_ciphertext : ℚ × (ℚ × ℚ) :=
  toyAEAD.encrypt
    (X3DH_SK_Alice toyKDF alice_IK.priv alice_EK.priv
      bob_IK.pub bob_SPK.pub (some bob_OPK.pub))
    alice_msg
    (alice_IK.pub, bob_IK.pub)

/-- End-to-end correctness: Bob decrypts Alice's ciphertext and recovers
the original message 42. Uses `X3DH_handshake_correct` with KeyPairs. -/
theorem bob_decrypts_alice :
    toyAEAD.decrypt
      (X3DH_SK_Bob toyKDF bob_IK.priv bob_SPK.priv
        (some bob_OPK.priv) alice_IK.pub alice_EK.pub)
      alice_ciphertext
      (alice_IK.pub, bob_IK.pub) = some alice_msg :=
  X3DH_handshake_correct toyKDF toyAEAD
    alice_IK alice_EK bob_IK bob_SPK (some bob_OPK)
    alice_msg alice_ciphertext rfl
