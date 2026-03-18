import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "../.."
set_option verso.exampleModule "PQXDHLean.X3DH"

#doc (Manual) "The X3DH Protocol" =>
%%%
tag := "x3dh"
%%%

# Key pairs

A key pair is a private scalar and the corresponding public key `[scalar]G`.

:::paragraph
```anchor X3DHKeyPair
structure KeyPair (G : Type _) [AddCommGroup G] where
  priv : ℕ
  pub : G
  gen : G
  pub_eq : pub = DH priv gen
```
:::

# X3DH shared secret computation

The four DH outputs computed by {anchorTerm X3DH_Alice}`X3DH_Alice` and {anchorTerm X3DHBob}`X3DH_Bob`.

:::paragraph
```anchor X3DH_Alice
noncomputable def X3DH_Alice
    (ikₐ ekₐ : ℕ) (IKᵦ SPKᵦ OPKᵦ : G) : G × G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ, DH ekₐ OPKᵦ)
```
:::

:::paragraph
```anchor X3DHBob
noncomputable def X3DH_Bob
    (ikᵦ spkᵦ opkᵦ : ℕ) (IKₐ EKₐ : G) : G × G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ, DH opkᵦ EKₐ)
```
:::

# Correctness

The core theorem: if all public keys are honestly generated from the
same generator G, then Alice and Bob compute identical DH tuples.

The correctness theorem {anchorTerm X3DHCorrectness}`X3DH_agree` states
that if all public keys are generated from the same generator, then Alice and Bob compute the same four DH values:

:::paragraph
```anchor X3DHCorrectness
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
```
:::

# Session key derivation

After computing the DH tuple, both parties feed it into a KDF to obtain
a single session key SK. Since the DH tuples are equal (by {anchorTerm X3DHCorrectness}`X3DH_agree`),
the derived session keys are equal.

{anchorTerm X3DHSKAlice}`X3DH_SK_Alice` and {anchorTerm X3DHSKBob}`X3DH_SK_Bob` session keys are KDF applied to their four DH values.

:::paragraph
```anchor X3DHSKAlice
noncomputable def X3DH_SK_Alice
    (kdf : KDF (G × G × G × G) SK)
    (ikₐ ekₐ : ℕ) (IKᵦ SPKᵦ OPKᵦ : G) : SK :=
  kdf.derive (X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ)
```
:::

:::paragraph
```anchor X3DHSKBob
noncomputable def X3DH_SK_Bob
    (kdf : KDF (G × G × G × G) SK)
    (ikᵦ spkᵦ opkᵦ : ℕ) (IKₐ EKₐ : G) : SK :=
  kdf.derive (X3DH_Bob ikᵦ spkᵦ opkᵦ IKₐ EKₐ)
```
:::

{anchorTerm X3DHSessionKeyAgreement}`X3DH_session_key_agree`: Alice and Bob derive the same session key.
:::paragraph
```anchor X3DHSessionKeyAgreement
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
```
:::

# Handshake: first authenticated message

Alice encrypts her first message using AEAD with:
  - key = SK (the derived session key)
  - associated data AD = IKₐᵖᵏ || IKᵦᵖᵏ (Figure 1, Bhargavan et al.)

The prose in Section 2.1 says AD "includes an encoding of" the two
identity public keys; Figure 1 gives the exact definition AD = IKₐ || IKᵦ.
We follow Figure 1 and model AD as G x G.

Bob decrypts with his SK and the same AD. If decryption succeeds,
the handshake is complete: both parties are authenticated and share
a secret session key.

{anchorTerm X3DHHandshakeCorrectness}`X3DH_handshake_correct`: Bob can decrypt Alice's first message.
This is the end-to-end correctness theorem for X3DH. It composes
DH agreement ({anchorTerm X3DHCorrectness}`X3DH_agree`),
session key agreement ({anchorTerm X3DHSessionKeyAgreement}`X3DH_session_key_agree`, via KDF),
and AEAD correctness.

:::paragraph
```anchor X3DHHandshakeCorrectness
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
```
:::
