import Verso
import VersoManual
import PQXDHDocs.DocX3DHPassiveSecrecy
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "The X3DH Protocol" =>

X3DH (Extended Triple Diffie-Hellman) key agreement protocol,
following Bhargavan et al. (USENIX Security 2024).

# Key pairs

A key pair binds a private scalar (in a field F) to its public key
(a group element), derived from a shared generator. The generator
is a type parameter, enforcing that all key pairs in a session share
the same generator by construction.

```
structure KeyPair (F G : Type _) [Field F] [AddCommGroup G] [Module F G]
    (G₀ : G) where
  priv : F
  pub : G
  pub_eq : pub = DH priv G₀
```

# Shared secret computation

Alice and Bob each compute four DH values:
- DH1 = DH(ikₐ, SPKᵦ) — mutual authentication (Alice's identity)
- DH2 = DH(ekₐ, IKᵦ) — mutual authentication (Bob's identity)
- DH3 = DH(ekₐ, SPKᵦ) — forward secrecy
- DH4 = DH(ekₐ, OPKᵦ) — replay protection (when OPK is present)

When OPK is absent, DH4 defaults to 0 (the group identity).

```
def X3DH_Alice
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ : G) (OPKᵦ : Option G) : G × G × G × G :=
  (DH ikₐ SPKᵦ, DH ekₐ IKᵦ, DH ekₐ SPKᵦ, DH ekₐ (OPKᵦ.getD 0))

def X3DH_Bob
    (ikᵦ spkᵦ : F) (opkᵦ : Option F) (IKₐ EKₐ : G) : G × G × G × G :=
  (DH spkᵦ IKₐ, DH ikᵦ EKₐ, DH spkᵦ EKₐ, DH (opkᵦ.getD 0) EKₐ)
```

# Correctness

If all key pairs are honestly generated from the same generator,
then Alice and Bob compute identical DH tuples:

```
theorem X3DH_agree
    {G₀ : G}
    (ikₐ ekₐ : KeyPair F G G₀)
    (ikᵦ spkᵦ : KeyPair F G G₀)
    (opkᵦ : Option (KeyPair F G G₀)) :
    X3DH_Alice ikₐ.priv ekₐ.priv ikᵦ.pub spkᵦ.pub (opkᵦ.map KeyPair.pub) =
    X3DH_Bob ikᵦ.priv spkᵦ.priv (opkᵦ.map KeyPair.priv) ikₐ.pub ekₐ.pub
```

The proof works by cases on OPK, then applies `simp` with the
`Module F G` lemmas (`smul_smul`, `mul_comm`) plus each key pair's
generation equation.

*Session key derivation*

Both parties feed the DH tuple into a KDF to obtain a session key:

```
def X3DH_SK_Alice (kdf : KDF (G × G × G × G) SK)
    (ikₐ ekₐ : F) (IKᵦ SPKᵦ : G) (OPKᵦ : Option G) : SK :=
  kdf.derive (X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ OPKᵦ)
```

Since the DH tuples are equal (by `X3DH_agree`), the derived session
keys are equal (`X3DH_session_key_agree`).

*Handshake correctness*

End-to-end correctness: Bob can decrypt Alice's first message.

```
theorem X3DH_handshake_correct
    (kdf : KDF (G × G × G × G) SK)
    (aead : AEAD SK PT CT_aead (G × G))
    {G₀ : G}
    (ikₐ ekₐ ikᵦ spkᵦ : KeyPair F G G₀)
    (opkᵦ : Option (KeyPair F G G₀))
    (msg : PT) (ct : CT_aead)
    (h_enc : ct = aead.encrypt (X3DH_SK_Alice kdf ...) msg (ikₐ.pub, ikᵦ.pub)) :
    aead.decrypt (X3DH_SK_Bob kdf ...) ct (ikₐ.pub, ikᵦ.pub) = some msg
```

This composes DH agreement, session key agreement via KDF,
and AEAD correctness.

{include 1 PQXDHDocs.DocX3DHPassiveSecrecy}
