import VersoManual
import VersoBlueprint
import PQXDHLean.AEAD

open Verso.Genre Manual
open Informal

set_option verso.exampleProject ".."
set_option verso.exampleModule "PQXDHLean.AEAD"

#doc (Manual) "Authenticated Encryption with Associated Data" =>
%%%
tag := "aead"
%%%

:::group "aead_core"
Core interface and correctness for authenticated encryption.
:::

An AEAD scheme provides both confidentiality and integrity for a
plaintext message, while binding the ciphertext to unencrypted
associated data (AD). In X3DH/PQXDH:

- The session key SK (derived by the KDF) is the AEAD key.
- Alice encrypts her first message using SK.
- The associated data AD = IKₐᵖᵏ ‖ IKᵦᵖᵏ binds the ciphertext
  to both parties' identities, preventing key-mismatch attacks.

The concrete instantiation is AES-256 in CBC mode with HMAC
(Encrypt-Then-Mac). The paper assumes IND-CPA and IND-CTXT,
which together imply IND-CCA2 for AEAD schemes (section 2.5, assumption 3).

# Structure

:::definition "aead_spec" (lean := "AEAD") (parent := "aead_core")
An AEAD is modeled by encrypt and decrypt operations together with an honest
round-trip correctness guarantee. The structure is parameterized by key type
`K` (session key from {uses "kdf_spec"}[]), plaintext type `PT`, ciphertext
type `CT`, and associated data type `AD`. The built-in `correctness` field
guarantees that decrypting an honestly encrypted ciphertext with the correct
key and AD always recovers the original plaintext.
:::
