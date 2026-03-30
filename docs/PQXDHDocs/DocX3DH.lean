import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.X3DH
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

A key pair binds a private scalar to its public key, derived from a
shared generator `G₀`. The generator is a type parameter, so all
`KeyPair F G G₀` values share the same `G₀` by construction.

```
structure KeyPair (F G : Type _) [Field F] [AddCommGroup G] [Module F G]
    (G₀ : G) where
  priv : F
  pub : G
  pub_eq : pub = DH priv G₀
```

# X3DH shared secret computation

Alice and Bob each compute DH values from their private keys
and the other party's public keys. OPK is optional; when absent,
DH4 defaults to 0 (the group identity).

:::definition "X3DH-Alice" (lean := "X3DH_Alice") (parent := "x3dh")
Alice's DH outputs: DH(ikₐ, SPKᵦ), DH(ekₐ, IKᵦ), DH(ekₐ, SPKᵦ), DH(ekₐ, OPKᵦ).
OPKᵦ is `Option G`.
:::

:::definition "X3DH-Bob" (lean := "X3DH_Bob") (parent := "x3dh")
Bob's DH outputs (mirror of Alice's). opkᵦ is `Option F`.
:::

# Correctness

The core theorem: if all key pairs are honestly generated from the
same generator G₀, then Alice and Bob compute identical DH tuples.

:::theorem "X3DH-agree" (lean := "X3DH_agree") (parent := "x3dh_correctness")
Alice and Bob compute the same four DH values, for any choice of OPK
(including none). Stated in terms of `KeyPair F G G₀`.
:::

:::proof "X3DH-agree"
By cases on OPK, then `simp` with `smul_smul` and `mul_comm` from the
`Module F G` API plus each key pair's `pub_eq`.
:::

# Session key derivation

After computing the DH tuple, both parties feed it into a KDF to obtain
a single session key SK. Since the DH tuples are equal (by `X3DH_agree`),
the derived session keys are equal.

:::definition "X3DH-SK-Alice" (lean := "X3DH_SK_Alice") (parent := "x3dh_session")
Alice's session key: KDF applied to her DH values.
:::

:::definition "X3DH-SK-Bob" (lean := "X3DH_SK_Bob") (parent := "x3dh_session")
Bob's session key: KDF applied to his DH values.
:::

:::theorem "X3DH-session-key-agree" (lean := "X3DH_session_key_agree") (parent := "x3dh_session")
Alice and Bob derive the same session key.
:::

:::proof "X3DH-session-key-agree"
By {uses "X3DH-agree"}[] and congruence through the KDF.
:::

# Handshake: first authenticated message

Alice encrypts her first message using AEAD with key = SK and
associated data AD = (IKₐ, IKᵦ). Bob decrypts with his SK and
the same AD.

:::theorem "X3DH-handshake-correct" (lean := "X3DH_handshake_correct") (parent := "x3dh_session")
Bob can decrypt Alice's first message.
Composes DH agreement ({uses "X3DH-agree"}[]),
session key agreement ({uses "X3DH-session-key-agree"}[], via KDF),
and AEAD correctness.
:::

:::proof "X3DH-handshake-correct"
By rewriting with {uses "X3DH-session-key-agree"}[] and applying AEAD correctness.
:::
