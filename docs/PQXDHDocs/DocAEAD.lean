import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Authenticated Encryption with Associated Data" =>

An AEAD scheme provides both confidentiality and integrity for a
plaintext message, while binding the ciphertext to unencrypted
associated data (AD).

# Structure

`AEAD K PT CT AD` has `encrypt`, `decrypt`, and a `correctness` field
guaranteeing that decrypting an honestly encrypted ciphertext with the
correct key and AD recovers the original plaintext.
