/-
X3DH (Extended Triple Diffie-Hellman) key agreement protocol.

Definitions and theorems follow:

  Bhargavan, Jacomme, Kiefer, Schmidt.
  "Formal verification of the PQXDH Post-Quantum key agreement
   protocol for end-to-end secure messaging."
  USENIX Security 2024, §2.1 pp. 470, Figure 1 p. 471.

See also the Signal X3DH spec:
  https://signal.org/docs/specifications/x3dh/x3dh.pdf

All proofs rely on the `Module F G` API from `DH.lean`.
-/
import PQXDHLean.X3DH.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD

variable {F : Type _} [Field F]
variable {G : Type _} [AddCommGroup G] [Module F G]

/-! ## Key pairs

Each party holds key pairs (private scalar, public group element)
derived from a shared generator G₀. The generator is a type
parameter, so all `KeyPair F G G₀` values share the same G₀
by construction. -/

/-- A key pair: private scalar and public group element satisfying
pub = DH(priv, G₀). The paper defines four key types: identity (IK),
signed prekey (SPK), one-time prekey (OPK), and ephemeral (EK). -/
structure KeyPair (F G : Type _) [Field F] [AddCommGroup G] [Module F G]
    (G₀ : G) where
  priv : F
  pub : G
  pub_eq : pub = DH priv G₀

/-! ## X3DH shared secret computation

Alice and Bob each compute DH values from their private keys
and the other party's public keys:

  DH1 = DH(ikₐ, SPKᵦ)   — mutual authentication (Alice's identity)
  DH2 = DH(ekₐ, IKᵦ)    — mutual authentication (Bob's identity)
  DH3 = DH(ekₐ, SPKᵦ)   — forward secrecy
  DH4 = DH(ekₐ, OPKᵦ)   — replay protection (when OPK is present)

When OPK is absent, DH4 defaults to 0 (the group identity).
-/

/-- Alice's DH computations. OPKᵦ is optional; when absent, DH4 = 0. -/
def X3DH_Alice
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ : G) (OPKᵦ : Option G) : G × G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ, DH ekₐ (OPKᵦ.getD 0))

/-- Bob's DH computations (mirror of Alice's). -/
def X3DH_Bob
    (ikᵦ spkᵦ : F) (opkᵦ : Option F) (IKₐ EKₐ : G) : G × G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ, DH (opkᵦ.getD 0) EKₐ)

/-! ## Correctness

If all public keys are honestly generated from the same generator G₀,
then Alice and Bob compute identical DH tuples. This follows from
DH commutativity: DH(a, DH(b, G₀)) = DH(b, DH(a, G₀)). -/

/-- X3DH agreement: Alice and Bob compute identical DH tuples. -/
theorem X3DH_agree
    {G₀ : G}
    (ikₐ ekₐ : KeyPair F G G₀)
    (ikᵦ spkᵦ : KeyPair F G G₀)
    (opkᵦ : Option (KeyPair F G G₀)) :
    X3DH_Alice ikₐ.priv ekₐ.priv ikᵦ.pub spkᵦ.pub (opkᵦ.map KeyPair.pub) =
    X3DH_Bob ikᵦ.priv spkᵦ.priv (opkᵦ.map KeyPair.priv) ikₐ.pub ekₐ.pub := by
  cases opkᵦ with
  | none =>
    simp [X3DH_Alice, X3DH_Bob, DH,
      ikₐ.pub_eq, ekₐ.pub_eq, ikᵦ.pub_eq, spkᵦ.pub_eq,
      smul_smul, mul_comm]
  | some kp =>
    simp [X3DH_Alice, X3DH_Bob, DH,
      ikₐ.pub_eq, ekₐ.pub_eq, ikᵦ.pub_eq, spkᵦ.pub_eq, kp.pub_eq,
      smul_smul, mul_comm]

/-! ## Session key derivation

The DH values are concatenated and passed to a KDF:

  SK = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4)
-/

variable {SK : Type _}

/-- Alice derives the session key SKₐ = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4). -/
def X3DH_SK_Alice
    (kdf : KDF (G × G × G × G) SK)
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ : G) (OPKᵦ : Option G) : SK :=
  kdf.derive (X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ)

/-- Bob derives the session key SK_B = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4). -/
def X3DH_SK_Bob
    (kdf : KDF (G × G × G × G) SK)
    (ikᵦ spkᵦ : F) (opkᵦ : Option F) (IKₐ EKₐ : G) : SK :=
  kdf.derive (X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ)

/-- Session key agreement: SKₐ = SK_B.
Composes `X3DH_agree` with the determinism of the KDF. -/
theorem X3DH_session_key_agree
    (kdf : KDF (G × G × G × G) SK)
    {G₀ : G}
    (ikₐ ekₐ : KeyPair F G G₀)
    (ikᵦ spkᵦ : KeyPair F G G₀)
    (opkᵦ : Option (KeyPair F G G₀)) :
    X3DH_SK_Alice kdf ikₐ.priv ekₐ.priv ikᵦ.pub spkᵦ.pub (opkᵦ.map KeyPair.pub) =
    X3DH_SK_Bob kdf ikᵦ.priv spkᵦ.priv (opkᵦ.map KeyPair.priv) ikₐ.pub ekₐ.pub := by
  simp only [X3DH_SK_Alice, X3DH_SK_Bob, X3DH_agree ikₐ ekₐ ikᵦ spkᵦ opkᵦ]

/-! ## Handshake: first authenticated message

Alice encrypts her first message with an AEAD using the session key
and associated data AD = (IKₐ, IKᵦ). Bob derives the same session
key and decrypts. -/

variable {PT CT_aead : Type _}

/-- End-to-end handshake correctness: Bob can decrypt Alice's first message.
Composes DH agreement, KDF determinism, and AEAD correctness. -/
theorem X3DH_handshake_correct
    (kdf : KDF (G × G × G × G) SK)
    (aead : AEAD SK PT CT_aead (G × G))
    {G₀ : G}
    (ikₐ ekₐ : KeyPair F G G₀)
    (ikᵦ spkᵦ : KeyPair F G G₀)
    (opkᵦ : Option (KeyPair F G G₀))
    (msg : PT)
    (ct : CT_aead)
    (h_enc : ct = aead.encrypt
      (X3DH_SK_Alice kdf ikₐ.priv ekₐ.priv ikᵦ.pub spkᵦ.pub (opkᵦ.map KeyPair.pub))
      msg (ikₐ.pub, ikᵦ.pub)) :
    aead.decrypt
      (X3DH_SK_Bob kdf ikᵦ.priv spkᵦ.priv (opkᵦ.map KeyPair.priv) ikₐ.pub ekₐ.pub)
      ct (ikₐ.pub, ikᵦ.pub) = some msg := by
  rw [h_enc, X3DH_session_key_agree kdf ikₐ ekₐ ikᵦ spkᵦ opkᵦ]
  exact aead.correctness _ msg _
