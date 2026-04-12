import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.X3DH
import PQXDHDocs.SourceBlock
import PQXDHDocs.DocPermDraws
import PQXDHDocs.DocX3DHPassiveSecrecy

open Verso.Genre Manual
open Informal

set_option verso.exampleProject ".."
set_option verso.exampleModule "PQXDHLean.X3DH.X3DH"

#doc (Manual) "The X3DH Protocol" =>
%%%
tag := "x3dh"
%%%

:::group "x3dh_core"
Core X3DH definitions and end-to-end correctness results.
:::

X3DH (Extended Triple Diffie-Hellman) key agreement protocol,
following Bhargavan et al. (USENIX Security 2024).

# Key pairs

:::definition "x3dh_keypair" (lean := "KeyPair") (parent := "x3dh_core")
A key pair binds a private scalar (in a field F) to its public key
(a group element), derived from a shared generator. The generator
is a type parameter, enforcing that all key pairs in a session share
the same generator by construction. The defining invariant is that
the public key is obtained by applying {uses "dh_spec"}[] to the
private scalar and the generator.
:::

# Shared secret computation

:::definition "x3dh_alice" (lean := "X3DH_Alice") (parent := "x3dh_core")
Alice computes four DH values from her private keys and Bob's public keys:
DH1 = DH(ik_a, SPK_b) for mutual authentication (Alice's identity),
DH2 = DH(ek_a, IK_b) for mutual authentication (Bob's identity),
DH3 = DH(ek_a, SPK_b) for forward secrecy,
DH4 = DH(ek_a, OPK_b) for replay protection (when OPK is present).
When OPK is absent, DH4 defaults to 0 (the group identity).
:::

:::definition "x3dh_bob" (lean := "X3DH_Bob") (parent := "x3dh_core")
Bob computes the same four DH values from his private keys and Alice's
public keys. The protocol is well-formed when Alice's and Bob's tuples
coincide.
:::

# Correctness

:::theorem "x3dh_agree" (lean := "X3DH_agree") (parent := "x3dh_core") (tags := "x3dh, agreement, classical") (effort := "medium") (priority := "high")
If all key pairs are honestly generated from the same generator, then Alice
and Bob compute identical DH tuples. The key algebraic input is
{uses "dh_spec"}[] commutativity.
:::

:::proof "x3dh_agree"
Work by cases on OPK, then apply `simp` with the `Module F G` lemmas
(`smul_smul`, `mul_comm`) plus each key pair's generation equation.
:::

```source X3DH_agree
```

# Session key derivation

:::definition "x3dh_sk_alice" (lean := "X3DH_SK_Alice") (parent := "x3dh_core")
Alice's session key is obtained by applying {uses "kdf_spec"}[] to
her DH tuple from {uses "x3dh_alice"}[].
:::

:::definition "x3dh_sk_bob" (lean := "X3DH_SK_Bob") (parent := "x3dh_core")
Bob's session key is obtained by applying {uses "kdf_spec"}[] to
his DH tuple from {uses "x3dh_bob"}[].
:::

:::theorem "x3dh_session_key_agree" (lean := "X3DH_session_key_agree") (parent := "x3dh_core") (tags := "x3dh, kdf, agreement") (effort := "small") (priority := "high")
Alice and Bob derive the same session key from the same {uses "kdf_spec"}[]
because the DH tuples agree by {uses "x3dh_agree"}[].
:::

:::proof "x3dh_session_key_agree"
Expand the two session-key definitions and rewrite the DH tuples using
{uses "x3dh_agree"}[].
:::

# Handshake: first authenticated message

Alice encrypts her first message using AEAD with the derived session
key and associated data AD = IK_a || IK_b (Figure 1, Bhargavan et al.).
Bob decrypts with his SK and the same AD. If decryption succeeds,
the handshake is complete.

:::theorem "x3dh_handshake_correct" (lean := "X3DH_handshake_correct") (parent := "x3dh_core") (tags := "x3dh, handshake, aead") (effort := "medium") (priority := "high")
Bob can decrypt Alice's first message. This theorem composes
{uses "x3dh_agree"}[], {uses "x3dh_session_key_agree"}[], and
{uses "aead_spec"}[] correctness.
:::

:::proof "x3dh_handshake_correct"
First identify Alice's and Bob's session keys using
{uses "x3dh_session_key_agree"}[]. Then rewrite the ciphertext hypothesis and
apply AEAD correctness.
:::

{include 1 PQXDHDocs.DocPermDraws}

{include 1 PQXDHDocs.DocX3DHPassiveSecrecy}
