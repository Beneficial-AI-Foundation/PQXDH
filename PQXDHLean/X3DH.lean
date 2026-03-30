/-
X3DH (Extended Triple Diffie-Hellman) key agreement protocol.

All proofs rely on the `Module F G` API from `DH.lean`, which covers
every algebraic property needed here (`smul_smul`, `mul_comm`, etc.).

Reference: Bhargavan et al. §2.1 pp. 470, Figure 1 p. 471.
         Signal X3DH spec: https://signal.org/docs/specifications/x3dh/x3dh.pdf
-/
import PQXDHLean.DH.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD

variable {F : Type _} [Field F]
variable {G : Type _} [AddCommGroup G] [Module F G]

/-! ## Key pairs -/

/-- §2.1, p. 470 "Key Generation": A key pair binds a private scalar to its
corresponding public key [scalar]·G. The paper defines four key types:
"A long term identity key IK", "a medium term key SPK", "a short term OPK",
and "short term ephemeral keys EK". For each key pair K, Kˢᵏ is the
private key and Kᵖᵏ is the public key. -/
structure KeyPair (F G : Type _) [Field F] [AddCommGroup G] [Module F G] where
  priv : F
  pub : G
  gen : G
  pub_eq : pub = DH priv gen

/-! ## X3DH shared secret computation -/

/-- §2.1, p. 470 "Session Secret Generation": Alice's four DH computations.
DH1 = (SPKᵦᵖᵏ)^{IKₐˢᵏ} — authenticates Alice,
DH2 = (IKᵦᵖᵏ)^{EKₐˢᵏ} — authenticates Bob,
DH3 = (SPKᵦᵖᵏ)^{EKₐˢᵏ} — forward secrecy,
DH4 = (OPKᵦᵖᵏ)^{EKₐˢᵏ} — replay protection (optional). -/
def X3DH_Alice
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ OPKᵦ : G) : G × G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ, DH ekₐ OPKᵦ)

/-- §2.1, p. 470 "Completing the Handshake": Bob's four DH computations
(mirror of Alice's by DH commutativity). "Blake performs the symmetric DH
computations, mutatis mutandis, and passes the concatenated values to the
KDF to obtain the final secret, SK_B." -/
def X3DH_Bob
    (ikᵦ spkᵦ opkᵦ : F) (IKₐ EKₐ : G) : G × G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ, DH opkᵦ EKₐ)

/-! ## Correctness -/

/-- §2.1, p. 470 "Completing the Handshake": X3DH agreement — if all public
keys are honestly generated from the same generator G₀, then Alice and Bob
compute identical DH tuples. The paper states: "This decryption is successful
if SKₐ = SK_B, and the protocol session is complete."
Follows from DH commutativity: a • (b • G₀) = b • (a • G₀), which is
`smul_smul` + `mul_comm` in the `Module F G` API. -/
theorem X3DH_agree
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : F)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀) :
    X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ =
    X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ; subst hOPKᵦ
  simp only [X3DH_Alice, X3DH_Bob, DH, smul_smul, mul_comm]

/-! ## Without one-time prekey -/

/-- §2.1, p. 470: Alice's three DH outputs when no one-time prekey is available.
"DH4 is optional, and only computed if OPKᵦᵖᵏ was provided." -/
def X3DH_Alice_no_OPK
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ : G) : G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ)

/-- §2.1, p. 470: Bob's three DH outputs when no one-time prekey is available. -/
def X3DH_Bob_no_OPK
    (ikᵦ spkᵦ : F) (IKₐ EKₐ : G) : G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ)

/-- §2.1, p. 470: X3DH agreement without the one-time prekey.
Same as `X3DH_agree` but with only three DH values. -/
theorem X3DH_agree_no_OPK
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ : F)
    {IKₐ EKₐ IKᵦ SPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀) :
    X3DH_Alice_no_OPK ikₐ ekₐ IKᵦ SPKᵦ =
    X3DH_Bob_no_OPK ikᵦ spkᵦ IKₐ EKₐ := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ
  simp only [X3DH_Alice_no_OPK, X3DH_Bob_no_OPK, DH, smul_smul, mul_comm]

/-! ## Session key derivation -/

variable {SK : Type _}

/-- §2.1, p. 470: Alice derives the session key SKₐ = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4).
"These three or four DH values are then concatenated and used inside a Key
Derivation Function (KDF) to obtain a session key SKₐ." -/
def X3DH_SK_Alice
    (kdf : KDF (G × G × G × G) SK)
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ OPKᵦ : G) : SK :=
  kdf.derive (X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ)

/-- §2.1, p. 470: Bob derives the session key SK_B = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4).
"Blake performs the symmetric DH computations [...] and passes the
concatenated values to the KDF to obtain the final secret, SK_B." -/
def X3DH_SK_Bob
    (kdf : KDF (G × G × G × G) SK)
    (ikᵦ spkᵦ opkᵦ : F) (IKₐ EKₐ : G) : SK :=
  kdf.derive (X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ)

/-- §2.1, p. 470: Alice and Bob derive the same session key (SKₐ = SK_B).
Composes `X3DH_agree` with the determinism of the KDF. -/
theorem X3DH_session_key_agree
    (kdf : KDF (G × G × G × G) SK)
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : F)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀) :
    X3DH_SK_Alice kdf ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ =
    X3DH_SK_Bob kdf ikᵦ spkᵦ opkᵦ IKₐ EKₐ := by
  simp only [X3DH_SK_Alice, X3DH_SK_Bob,
    X3DH_agree G₀ ikₐ ekₐ ikᵦ spkᵦ opkᵦ hIKₐ hEKₐ hIKᵦ hSPKᵦ hOPKᵦ]

/-! ## Handshake: first authenticated message -/

variable {PT CT_aead : Type _}

/-- §2.1, p. 470 "Session Secret Generation" and "Completing the Handshake":
End-to-end X3DH handshake correctness — Bob can decrypt Alice's first message.
Alice "encrypt[s] a first message with an AEAD, where the associated data
includes an encoding of IKₐᵖᵏ, IKᵦᵖᵏ". Bob "uses [SK_B] to decrypt the
AEAD ciphertext. This decryption is successful if SKₐ = SK_B".
Composes DH agreement, session key agreement (via KDF), and AEAD correctness. -/
theorem X3DH_handshake_correct
    (kdf : KDF (G × G × G × G) SK)
    (aead : AEAD SK PT CT_aead (G × G))
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : F)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀)
    (msg : PT)
    (ct : CT_aead)
    (h_enc : ct = aead.encrypt
      (X3DH_SK_Alice kdf ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ) msg (IKₐ, IKᵦ)) :
    aead.decrypt
      (X3DH_SK_Bob kdf ikᵦ spkᵦ opkᵦ IKₐ EKₐ) ct (IKₐ, IKᵦ) = some msg := by
  have h_sk := X3DH_session_key_agree kdf G₀
    ikₐ ekₐ ikᵦ spkᵦ opkᵦ hIKₐ hEKₐ hIKᵦ hSPKᵦ hOPKᵦ
  rw [h_enc, h_sk]
  exact aead.correctness _ msg _
