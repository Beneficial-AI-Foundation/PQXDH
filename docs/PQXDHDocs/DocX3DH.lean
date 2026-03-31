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

The paper defines four key types: identity (IK), signed prekey (SPK),
one-time prekey (OPK), and ephemeral (EK).

# Shared secret computation

Alice and Bob each compute four DH values from their private keys
and the other party's public keys:

- DH1 = DH(ikA, SPKB) -- mutual authentication (Alice's identity)
- DH2 = DH(ekA, IKB)  -- mutual authentication (Bob's identity)
- DH3 = DH(ekA, SPKB) -- forward secrecy
- DH4 = DH(ekA, OPKB) -- replay protection (when OPK is present)

When OPK is absent, DH4 defaults to 0 (the group identity).

# Correctness

If all key pairs are honestly generated from the same generator,
then Alice and Bob compute identical DH tuples. The proof works by
cases on the optional OPK, then applies simp with the Module F G API.

# Session key derivation

Both parties feed the DH tuple into a KDF to obtain a session key SK.
Since the DH tuples are equal, the derived session keys are equal.

# Handshake correctness

End-to-end correctness: Bob can decrypt Alice's first message. This
composes three results: DH agreement, session key agreement via KDF,
and AEAD correctness.

# Passive message secrecy

The passive secrecy property is formalized in a separate file,
described in the next section.
