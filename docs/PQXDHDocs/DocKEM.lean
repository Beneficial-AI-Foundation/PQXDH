import VersoManual
import VersoBlueprint
import PQXDHLean.KEM

open Verso.Genre Manual
open Informal


#doc (Manual) "Key Encapsulation Mechanism" =>
%%%
tag := "kem"
%%%

:::group "kem_core"
Core interface and correctness for the post-quantum KEM component.
:::

A KEM provides a way for two parties to establish a shared secret
using public-key cryptography. One party encapsulates (producing a
ciphertext and a shared secret); the other decapsulates (recovering
the shared secret from the ciphertext using their private key).

In PQXDH, the KEM adds post-quantum secure entropy to the key
exchange. Bob publishes a KEM public key (PQSPK). Alice
encapsulates to get (ct, ss), appends ss to her KDF input, and
sends ct to Bob. Bob decapsulates to recover ss.

The concrete instantiation is Kyber-1024 (ML-KEM), a lattice-based
KEM secure under the Module-LWE assumption (§2.5, p. 472, Bhargavan
et al.). The paper assumes the KEM is IND-CCA (section 2.5,
assumption 1.B).

# Structure

:::definition "kem_spec" (lean := "KEM") (parent := "kem_core")
A KEM is modeled by encapsulation and decapsulation operations together with
an honest round-trip property connecting them. The structure is parameterized
by public key type `PK`, secret key type `SK_kem`, ciphertext type `CT`,
and shared secret type `SS`. The built-in `correctness` field guarantees that
if `encaps pk = (ct, ss)`, then `decaps sk ct = ss`.
:::
