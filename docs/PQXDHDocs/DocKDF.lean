import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.KDF
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Key Derivation Function" =>

:::group "kdf"
KDF scheme
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

The `KDF` structure is parameterized by an input type `I`
(e.g., concatenation of DH outputs) and a key type `K` (the derived session key).
It has a single operation `derive` that deterministically maps input material to a key.

```
structure KDF (I K : Type _) where
  derive : I → K
```
