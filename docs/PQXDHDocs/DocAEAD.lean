import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "PQXDHLean.AEAD"

#doc (Manual) "Authenticated Encryption with Associated Data" =>
%%%
tag := "aead"
%%%

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

The {anchorTerm AEADStructure}`AEAD` structure is parameterized by key type `K` (session key from KDF),
plaintext type `PT`, ciphertext type `CT`, and associated data type `AD`.

It models encrypt and decrypt operations.
Encryption is deterministic given a nonce (which we fold into the key for abstraction).
Decryption returns `Option PT` to model authentication failure: `none` means the
ciphertext or AD was tampered with.
The built-in `correctness` field guarantees that decrypting an honestly encrypted
ciphertext with the correct key and AD always succeeds.

:::paragraph
```anchor AEADStructure
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt
```
:::

# Correctness theorems

{anchorTerm AEADDecryptEncrypt}`AEAD_decrypt_encrypt`: decrypting an honestly encrypted
ciphertext with the same key and associated data recovers the plaintext.

:::paragraph
```anchor AEADDecryptEncrypt
theorem AEAD_decrypt_encrypt {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k : K) (pt : PT) (ad : AD) :
    aead.decrypt k (aead.encrypt k pt ad) ad = some pt :=
  aead.correctness k pt ad
```
:::

{anchorTerm AEADAgree}`AEAD_agree`: if Alice and Bob share the same session key and
associated data, Bob can decrypt Alice's ciphertext.

:::paragraph
```anchor AEADAgree
theorem AEAD_agree {K PT CT AD : Type _} (aead : AEAD K PT CT AD)
    (k_a k_b : K) (pt : PT) (ad_a ad_b : AD) (ct : CT)
    (h_key : k_a = k_b) (h_ad : ad_a = ad_b)
    (h_enc : ct = aead.encrypt k_a pt ad_a) :
    aead.decrypt k_b ct ad_b = some pt := by
  subst h_key; subst h_ad; subst h_enc
  exact aead.correctness k_a pt ad_a
```
:::
