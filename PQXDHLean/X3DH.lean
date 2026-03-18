/-
X3DH (Extended Triple Diffie-Hellman) key agreement protocol.

Defines the protocol abstractly over any `AddCommGroup G` using the
abstract `DH` from DH.lean. No curve, field, or byte encoding is
mentioned — correctness depends only on DH commutativity.

Reference: https://signal.org/docs/specifications/x3dh/x3dh.pdf

## Protocol overview

Alice wants to establish a shared secret with Bob.

Bob publishes a "prekey bundle":
  - IKᵦ = [ikᵦ]G   (long-term identity key)
  - SPKᵦ = [spkᵦ]G  (signed prekey, medium-term)
  - OPKᵦ = [opkᵦ]G  (one-time prekey, optional)

Alice has her own identity key pair (ikₐ, IKₐ = [ikₐ]G) and generates
an ephemeral key pair (ekₐ, EKₐ = [ekₐ]G).

Alice computes:
  DH1 = DH(ikₐ,  SPKᵦ)   — authenticates Alice
  DH2 = DH(ekₐ,  IKᵦ)    — authenticates Bob
  DH3 = DH(ekₐ,  SPKᵦ)   — forward secrecy
  DH4 = DH(ekₐ,  OPKᵦ)   — replay protection (optional)

Bob computes the same values (by DH commutativity):
  DH1 = DH(spkᵦ, IKₐ)
  DH2 = DH(ikᵦ,  EKₐ)
  DH3 = DH(spkᵦ, EKₐ)
  DH4 = DH(opkᵦ, EKₐ)

## Security analysis of each DH

The key question for each DH: what private key must an attacker steal to
compute it?

### DH1 = DH(ikₐ, SPKᵦ) — authenticates Alice

Uses Alice's long-term private key `ikₐ`. Only Alice knows this scalar.
An attacker impersonating Alice cannot compute DH1 without stealing `ikₐ`.
This binds the session to Alice's identity.

No forward secrecy: `ikₐ` is reused across all sessions. If `ikₐ` is
compromised later, an attacker who recorded past sessions can recompute
DH1 for all of them.

### DH2 = DH(ekₐ, IKᵦ) — authenticates Bob

Uses Bob's long-term private key `ikᵦ`. Only Bob knows this scalar.
An attacker who serves a fake prekey bundle (impersonating Bob) cannot
compute DH2 without stealing `ikᵦ`. This binds the session to Bob's
identity.

Same caveat: no forward secrecy, since `ikᵦ` is long-lived.

### DH1 + DH2 together = mutual authentication

DH1 requires `ikₐ` (proves Alice is Alice). DH2 requires `ikᵦ` (proves
Bob is Bob). An attacker must compromise *both* identity keys to fully
break authentication.

### DH3 = DH(ekₐ, SPKᵦ) — forward secrecy

Uses only ephemeral (`ekₐ`) and medium-term (`spkᵦ`) keys — no long-term
identity keys. Both are deleted after use (`ekₐ` immediately, `spkᵦ` after
rotation).

Even if both `ikₐ` and `ikᵦ` are compromised later, the attacker still
cannot compute DH3, because the ephemeral key `ekₐ` no longer exists.
Past sessions remain secret. This is the essential forward secrecy
guarantee.

### DH4 = DH(ekₐ, OPKᵦ) — replay protection (optional)

The one-time prekey `opkᵦ` is used exactly once, then deleted from Bob's
server. If an attacker records Alice's initial message and replays it, Bob
will reject it because the OPK has already been consumed. Without DH4, an
attacker could replay the initial message, causing Bob to establish a
duplicate session.

### Combined: SK = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4)

All four values are concatenated and fed to a KDF. The shared secret SK
is only computable by someone who knows at least one private key from
each DH. The security degrades gracefully: compromising one key does not
break all properties.

### Key lifetime summary

  IK  (identity):    generated once at install, never deleted
  SPK (signed):      rotated periodically (e.g. weekly)
  OPK (one-time):    consumed after single use, then deleted
  EK  (ephemeral):   generated per session, deleted immediately after use
-/
import PQXDHLean.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD

variable {G : Type _} [AddCommGroup G]

/-! ## Key pairs

A key pair is a private scalar and the corresponding public key `[scalar]G`.
-/

-- ANCHOR: X3DHKeyPair
structure KeyPair (G : Type _) [AddCommGroup G] where
  priv : ℕ
  pub : G
  gen : G
  pub_eq : pub = DH priv gen
-- ANCHOR_END: X3DHKeyPair

/-! ## X3DH shared secret computation

Alice's and Bob's views of the four DH values.
-/

-- ANCHOR: X3DH_Alice
noncomputable def X3DH_Alice
    (ikₐ ekₐ : ℕ) (IKᵦ SPKᵦ OPKᵦ : G) : G × G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ, DH ekₐ OPKᵦ)
-- ANCHOR_END: X3DH_Alice

-- ANCHOR: X3DHBob
noncomputable def X3DH_Bob
    (ikᵦ spkᵦ opkᵦ : ℕ) (IKₐ EKₐ : G) : G × G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ, DH opkᵦ EKₐ)
-- ANCHOR_END: X3DHBob

/-! ## Correctness

The core theorem: if all public keys are honestly generated from the
same generator G, then Alice and Bob compute identical DH tuples.
-/

-- ANCHOR: X3DHCorrectness
theorem X3DH_agree
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : ℕ)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀) :
    X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ =
    X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ; subst hOPKᵦ
  simp only [X3DH_Alice, X3DH_Bob, DH_comm]
--ANCHOR_END: X3DHCorrectness

/-! ## Without one-time prekey

X3DH also works without OPK (DH4 is omitted). We model this as the
3-DH variant.
-/

/-- Alice's three DH outputs (no one-time prekey). -/
noncomputable def X3DH_Alice_no_OPK
    (ikₐ ekₐ : ℕ) (IKᵦ SPKᵦ : G) : G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ)

/-- Bob's three DH outputs (no one-time prekey). -/
noncomputable def X3DH_Bob_no_OPK
    (ikᵦ spkᵦ : ℕ) (IKₐ EKₐ : G) : G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ)

/-- X3DH correctness without one-time prekey. -/
theorem X3DH_agree_no_OPK
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ : ℕ)
    {IKₐ EKₐ IKᵦ SPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀) :
    X3DH_Alice_no_OPK ikₐ ekₐ IKᵦ SPKᵦ =
    X3DH_Bob_no_OPK ikᵦ spkᵦ IKₐ EKₐ := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ
  simp only [X3DH_Alice_no_OPK, X3DH_Bob_no_OPK, DH_comm]

/-! ## Session key derivation

After computing the DH tuple, both parties feed it into a KDF to obtain
a single session key SK. Since the DH tuples are equal (by `X3DH_agree`),
the derived session keys are equal.
-/

variable {SK : Type _}

-- ANCHOR: X3DHSKAlice
noncomputable def X3DH_SK_Alice
    (kdf : KDF (G × G × G × G) SK)
    (ikₐ ekₐ : ℕ) (IKᵦ SPKᵦ OPKᵦ : G) : SK :=
  kdf.derive (X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ)
-- ANCHOR_END: X3DHSKAlice

-- ANCHOR: X3DHSKBob
noncomputable def X3DH_SK_Bob
    (kdf : KDF (G × G × G × G) SK)
    (ikᵦ spkᵦ opkᵦ : ℕ) (IKₐ EKₐ : G) : SK :=
  kdf.derive (X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ)
-- ANCHOR_END: X3DHSKBob

-- ANCHOR: X3DHSessionKeyAgreement
theorem X3DH_session_key_agree
    (kdf : KDF (G × G × G × G) SK)
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : ℕ)
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
-- ANCHOR_END: X3DHSessionKeyAgreement

/-! ## Handshake: first authenticated message

Alice encrypts her first message using AEAD with:
  - key = SK (the derived session key)
  - associated data AD = IKₐᵖᵏ || IKᵦᵖᵏ (Figure 1, Bhargavan et al.)

The prose in Section 2.1 says AD "includes an encoding of" the two
identity public keys; Figure 1 gives the exact definition AD = IKₐ || IKᵦ.
We follow Figure 1 and model AD as G x G.

Bob decrypts with his SK and the same AD. If decryption succeeds,
the handshake is complete: both parties are authenticated and share
a secret session key.
-/

variable {PT CT_aead : Type _}

-- ANCHOR: X3DHHandshakeCorrectness
theorem X3DH_handshake_correct
    (kdf : KDF (G × G × G × G) SK)
    (aead : AEAD SK PT CT_aead (G × G))
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : ℕ)
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
-- ANCHOR_END: X3DHHandshakeCorrectness
