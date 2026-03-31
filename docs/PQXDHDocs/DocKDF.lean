import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Key Derivation Function" =>

A KDF deterministically derives a fixed-size key from variable-length
input material. In X3DH the input is the concatenation of the
DH outputs and the result is the session key SK.

# Structure

`KDF I K` has a single field `derive : I → K`.

# Random Oracle Model

In the security proof, the KDF is modeled as a random oracle using
VCV-io's `KDFOracle (I K) := I →ₒ K` and `randomOracle` implementation.
