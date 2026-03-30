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
input material. In X3DH the input is the concatenation of the
DH outputs and the result is the session key SK.

# Structure

:::definition "KDF" (lean := "KDF") (parent := "kdf")
`KDF I K` has a single field `derive : I → K`.
:::
