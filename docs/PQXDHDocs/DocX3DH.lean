import Verso
import VersoManual
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
    (G0 : G) where
  priv : F
  pub : G
  pub_eq : pub = DH priv G0
```

# Shared secret computation

Alice and Bob each compute four DH values. OPK is optional; when
absent, DH4 defaults to 0 (the group identity).

```
def X3DH_Alice
    (ikA ekA : F) (IKB SPKB : G) (OPKB : Option G) : G * G * G * G :=
  (DH ikA SPKB, DH ekA IKB, DH ekA SPKB, DH ekA (OPKB.getD 0))

def X3DH_Bob
    (ikB spkB : F) (opkB : Option F) (IKA EKA : G) : G * G * G * G :=
  (DH spkB IKA, DH ikB EKA, DH spkB EKA, DH (opkB.getD 0) EKA)
```

# Correctness

If all key pairs are honestly generated from the same generator,
then Alice and Bob compute identical DH tuples:

```
theorem X3DH_agree
    {G0 : G}
    (ikA ekA : KeyPair F G G0)
    (ikB spkB : KeyPair F G G0)
    (opkB : Option (KeyPair F G G0)) :
    X3DH_Alice ikA.priv ekA.priv ikB.pub spkB.pub (opkB.map KeyPair.pub) =
    X3DH_Bob ikB.priv spkB.priv (opkB.map KeyPair.priv) ikA.pub ekA.pub
```

The proof works by cases on OPK, then applies simp with the
Module F G lemmas plus each key pair's generation equation.

# Session key derivation

Both parties feed the DH tuple into a KDF to obtain a session key:

```
def X3DH_SK_Alice (kdf : KDF (G * G * G * G) SK)
    (ikA ekA : F) (IKB SPKB : G) (OPKB : Option G) : SK :=
  kdf.derive (X3DH_Alice ikA ekA IKB SPKB OPKB)
```

Since the DH tuples are equal (by X3DH_agree), the derived session
keys are equal (X3DH_session_key_agree).

# Handshake correctness

End-to-end correctness: Bob can decrypt Alice's first message.

```
theorem X3DH_handshake_correct
    (kdf : KDF (G * G * G * G) SK)
    (aead : AEAD SK PT CT_aead (G * G))
    {G0 : G}
    (ikA ekA ikB spkB : KeyPair F G G0)
    (opkB : Option (KeyPair F G G0))
    (msg : PT) (ct : CT_aead)
    (h_enc : ct = aead.encrypt (...) msg (ikA.pub, ikB.pub)) :
    aead.decrypt (...) ct (ikA.pub, ikB.pub) = some msg
```

This composes DH agreement, session key agreement via KDF,
and AEAD correctness.
