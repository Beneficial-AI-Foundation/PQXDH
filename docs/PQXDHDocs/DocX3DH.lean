import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "The X3DH Protocol" =>

X3DH (Extended Triple Diffie-Hellman) key agreement protocol,
following Bhargavan et al. (USENIX Security 2024).

# Key pairs

A key pair binds a private scalar to its public key, derived from a
shared generator. The generator is a type parameter, so all key pairs
share the same generator by construction.

# Shared secret computation

Alice and Bob each compute DH values from their private keys
and the other party's public keys. OPK is optional; when absent,
DH4 defaults to 0 (the group identity).

# Correctness

If all key pairs are honestly generated from the same generator,
then Alice and Bob compute identical DH tuples.

# Session key derivation

Both parties feed the DH tuple into a KDF. Since the tuples are
equal, the derived session keys are equal.

# Handshake correctness

Bob can decrypt Alice's first message. This composes DH agreement,
session key agreement (via KDF), and AEAD correctness.

# Passive message secrecy

The passive secrecy property formalizes that a passive eavesdropper
cannot distinguish the session key from random, under the Random
Oracle Model for the KDF.

The security game uses VCV-io's ProbComp and randomOracle. The
reduction to DDH embeds the DDH challenge as DH3, and the main
theorem bounds the passive secrecy advantage by the DDH advantage.
