import VersoManual
import VersoBlueprint
import PQXDHLean.KDF

open Verso.Genre Manual
open Informal


#doc (Manual) "Key Derivation Function" =>
%%%
tag := "kdf"
%%%

:::group "kdf_core"
Core interface for deterministic and random-oracle key derivation.
:::

A KDF deterministically derives a fixed-size key from variable-length
input material. In X3DH the input is the concatenation of the
DH outputs and the result is the session key SK.

The concrete instantiation is HKDF (RFC 5869) with SHA-256.

Two formalizations coexist, modeling different aspects of the KDF.

# Deterministic KDF

:::definition "kdf_spec" (lean := "KDF") (parent := "kdf_core")
A KDF is modeled as a deterministic map from input material to a derived key.
The abstraction is intentionally minimal so protocol proofs can reason only
about equality of derived outputs from equal transcripts.
Used in the correctness proofs ({uses "x3dh_agree"}[], {uses "x3dh_handshake_correct"}[]),
which only need "same input implies same output" --- no randomness or
security assumptions.
:::

# Random Oracle KDF

:::definition "kdf_oracle" (lean := "KDFOracle") (parent := "kdf_core")
An oracle type `I -> K` implemented by VCV-io's `randomOracle`
(lazy cached uniform sampling). Used in the security proofs
(passive message secrecy), where the KDF is modeled as a random
oracle per the paper's assumption 4 (section 2.5).
:::

The paper makes the same distinction: correctness is unconditional,
security assumes the ROM.
