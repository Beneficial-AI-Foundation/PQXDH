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

```
structure AEAD (K PT CT AD : Type _) where
  encrypt : K → PT → AD → CT
  decrypt : K → CT → AD → Option PT
  correctness : ∀ (k : K) (pt : PT) (ad : AD),
    decrypt k (encrypt k pt ad) ad = some pt
```

The `correctness` field guarantees that decrypting an honestly
encrypted ciphertext with the correct key and AD recovers the
original plaintext. In X3DH, the associated data is the pair
`(IKₐ, IKᵦ)` of identity public keys.
