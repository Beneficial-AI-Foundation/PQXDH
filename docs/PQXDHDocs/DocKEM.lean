import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.KEM
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Key Encapsulation Mechanism" =>

:::group "kem"
KEM scheme
:::

A KEM provides a way for two parties to establish a shared secret
using public-key cryptography. One party encapsulates (producing a
ciphertext and a shared secret); the other decapsulates (recovering
the shared secret from the ciphertext using their private key).

# Structure

:::definition "KEM" (parent := "kem")
`KEM PK SK_kem CT SS` has `encaps`, `decaps`, and a `correctness` field
guaranteeing that honest encapsulation/decapsulation round-trips.
:::
