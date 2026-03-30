import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.AEAD
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

:::group "aead"
AEAD scheme
:::

An AEAD scheme provides both confidentiality and integrity for a
plaintext message, while binding the ciphertext to unencrypted
associated data (AD).

# Structure

:::definition "AEAD" (lean := "AEAD") (parent := "aead")
`AEAD K PT CT AD` has `encrypt`, `decrypt`, and a `correctness` field
guaranteeing that decrypting an honestly encrypted ciphertext with the
correct key and AD recovers the original plaintext.
:::
