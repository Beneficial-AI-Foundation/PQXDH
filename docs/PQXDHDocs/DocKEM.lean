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

-- # Structure

```
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss
```

The `correctness` field guarantees that honest
encapsulation/decapsulation round-trips: if `encaps pk = (ct, ss)`,
then `decaps sk ct = ss`.

In PQXDH, the KEM adds post-quantum resistance on top of the
classical X3DH DH values. The KEM shared secret is concatenated
with the DH outputs before being passed to the KDF.
