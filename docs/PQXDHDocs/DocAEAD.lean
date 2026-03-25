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

:::group "aead_correctness"
Correctness properties of AEAD.
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
which together imply IND-CCA2 for AEAD schemes (§2.5, assumption 3).

# Structure

The `AEAD` structure is parameterized by key type `K` (session key from KDF),
plaintext type `PT`, ciphertext type `CT`, and associated data type `AD`.
It models encrypt and decrypt operations.
Encryption is deterministic given a nonce (which we fold into the key for abstraction).
Decryption returns `Option PT` to model authentication failure: `none` means the
ciphertext or AD was tampered with.
The built-in `correctness` field guarantees that decrypting an honestly encrypted
ciphertext with the correct key and AD always succeeds.

```
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt
```

# Correctness theorems

:::theorem "AEAD-decrypt-encrypt" (lean := "AEAD_decrypt_encrypt") (parent := "aead_correctness")
Decrypting an honestly encrypted ciphertext with the same key and associated data recovers the plaintext.
:::

:::proof "AEAD-decrypt-encrypt"
Follows directly from the `correctness` field of the AEAD structure.

```
aead.correctness k pt ad
```
:::

:::theorem "AEAD-agree" (lean := "AEAD_agree") (parent := "aead_correctness")
If Alice and Bob share the same session key and associated data, Bob can decrypt Alice's ciphertext.
:::

:::proof "AEAD-agree"
By substitution of equal keys and associated data, then applying `correctness`.

```
subst h_key; subst h_ad; subst h_enc
exact aead.correctness k_a pt ad_a
```
:::
