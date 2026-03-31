import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Key Encapsulation Mechanism" =>

A KEM provides a way for two parties to establish a shared secret
using public-key cryptography. One party encapsulates (producing a
ciphertext and a shared secret); the other decapsulates (recovering
the shared secret from the ciphertext using their private key).

# Structure

`KEM PK SK_kem CT SS` has `encaps`, `decaps`, and a `correctness` field
guaranteeing that honest encapsulation/decapsulation round-trips.
