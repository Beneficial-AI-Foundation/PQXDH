import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "The X3DH Protocol" =>

:::group "x3dh"
X3DH protocol
:::

:::group "x3dh_correctness"
Correctness properties of X3DH.
:::

:::group "x3dh_session"
Session key derivation and handshake.
:::

# Key pairs

A key pair is a private scalar and the corresponding public key `[scalar]G`.

```
structure KeyPair (G : Type _) [AddCommGroup G] where
  priv : ℕ
  pub : G
  gen : G
  pub_eq : pub = DH priv gen
```

# X3DH shared secret computation

The four DH outputs computed by Alice and Bob.

:::definition "X3DH-Alice" (lean := "X3DH_Alice") (parent := "x3dh")
Alice's four DH outputs: DH(ikₐ, SPKᵦ), DH(ekₐ, IKᵦ), DH(ekₐ, SPKᵦ), DH(ekₐ, OPKᵦ).
:::

:::definition "X3DH-Bob" (lean := "X3DH_Bob") (parent := "x3dh")
Bob's four DH outputs: DH(spkᵦ, IKₐ), DH(ikᵦ, EKₐ), DH(spkᵦ, EKₐ), DH(opkᵦ, EKₐ).
:::

# Correctness

The core theorem: if all public keys are honestly generated from the
same generator G, then Alice and Bob compute identical DH tuples.

:::theorem "X3DH-agree" (lean := "X3DH_agree") (parent := "x3dh_correctness")
If all public keys are generated from the same generator, then Alice and Bob compute the same four DH values.
:::

:::proof "X3DH-agree"
By substitution of the key generation equations and DH commutativity.

```
subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ; subst hOPKᵦ
simp only [X3DH_Alice, X3DH_Bob, DH_comm]
```
:::

# Session key derivation

After computing the DH tuple, both parties feed it into a KDF to obtain
a single session key SK. Since the DH tuples are equal (by `X3DH_agree`),
the derived session keys are equal.

:::definition "X3DH-SK-Alice" (lean := "X3DH_SK_Alice") (parent := "x3dh_session")
Alice's session key: KDF applied to her four DH values.
:::

:::definition "X3DH-SK-Bob" (lean := "X3DH_SK_Bob") (parent := "x3dh_session")
Bob's session key: KDF applied to his four DH values.
:::

:::theorem "X3DH-session-key-agree" (lean := "X3DH_session_key_agree") (parent := "x3dh_session")
Alice and Bob derive the same session key.
:::

:::proof "X3DH-session-key-agree"
By {uses "X3DH-agree"}[] and congruence through the KDF.

```
simp only [X3DH_SK_Alice, X3DH_SK_Bob,
  X3DH_agree G₀ ikₐ ekₐ ikᵦ spkᵦ opkᵦ hIKₐ hEKₐ hIKᵦ hSPKᵦ hOPKᵦ]
```
:::

# Handshake: first authenticated message

Alice encrypts her first message using AEAD with:
- key = SK (the derived session key)
- associated data AD = IKₐᵖᵏ ‖ IKᵦᵖᵏ (Figure 1, Bhargavan et al.)

The prose in Section 2.1 says AD "includes an encoding of" the two
identity public keys; Figure 1 gives the exact definition AD = IKₐ ‖ IKᵦ.
We follow Figure 1 and model AD as G × G.

Bob decrypts with his SK and the same AD. If decryption succeeds,
the handshake is complete: both parties are authenticated and share
a secret session key.

:::theorem "X3DH-handshake-correct" (lean := "X3DH_handshake_correct") (parent := "x3dh_session")
Bob can decrypt Alice's first message.
This is the end-to-end correctness theorem for X3DH. It composes
DH agreement ({uses "X3DH-agree"}[]),
session key agreement ({uses "X3DH-session-key-agree"}[], via KDF),
and AEAD correctness.
:::

:::proof "X3DH-handshake-correct"
By rewriting with {uses "X3DH-session-key-agree"}[] and applying AEAD correctness.

```
have h_sk := X3DH_session_key_agree kdf G₀
  ikₐ ekₐ ikᵦ spkᵦ opkᵦ hIKₐ hEKₐ hIKᵦ hSPKᵦ hOPKᵦ
rw [h_enc, h_sk]
exact aead.correctness _ msg _
```
:::
