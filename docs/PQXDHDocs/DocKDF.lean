import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option verso.exampleProject "."
set_option verso.exampleModule "PQXDHLean.KDF"

#doc (Manual) "Key Derivation Function" =>
%%%
tag := "kdf"
%%%

:::group "kdf_core"
Core interface for deterministic key derivation from protocol transcripts.
:::

A KDF deterministically derives a fixed-size key from variable-length
input material. In X3DH/PQXDH the input is the concatenation of the
DH outputs and the result is the session key SK.

The concrete instantiation is HKDF (RFC 5869) with SHA-256.
The paper assumes the KDF behaves as a random oracle: its output is
indistinguishable from a uniformly random key (§2.5, assumption 2).

We model a KDF as a single deterministic `derive` function.
Equal inputs yield equal outputs, which is trivially true for any function
but makes the structure explicit for downstream composition proofs.

# Structure

:::definition "kdf_spec" (parent := "kdf_core")
A KDF is modeled as a deterministic map from input material to a derived key.
The abstraction is intentionally minimal so protocol proofs can reason only
about equality of derived outputs from equal transcripts.
:::

The {anchorTerm KDFStructure}`KDF` structure is parameterized by an input type `I`
(e.g., concatenation of DH outputs) and a key type `K` (the derived session key).
It has a single operation `derive` that deterministically maps input material to a key.

:::paragraph
```anchor KDFStructure
structure KDF (I K : Type _) where
  derive : I → K
```
:::
