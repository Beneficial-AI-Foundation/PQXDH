import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option verso.exampleProject "."
set_option verso.exampleModule "PQXDHLean.KEM"

#doc (Manual) "Key Encapsulation Mechanism" =>
%%%
tag := "kem"
%%%

:::group "kem_core"
Core interface and correctness lemma for the post-quantum KEM component.
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
KEM secure under the Module-LWE assumption. The paper assumes the
KEM is IND-CCA: an attacker who sees the public key and ciphertext
cannot distinguish the shared secret from a random value, even with
access to a decapsulation oracle for other ciphertexts (§2.5, assumption 1.B).

In a real KEM, encapsulation is randomized — each call produces a
fresh (ct, ss) pair. We model encaps as a deterministic function
parameterized by the randomness, which is standard in formal
verification (the randomness is treated as an input rather than
being sampled internally).

# Structure

:::definition "kem_spec" (parent := "kem_core")
A KEM is modeled by encapsulation and decapsulation operations together with
an honest round-trip property connecting them.
:::

The {anchorTerm KEMStructure}`KEM` structure is parameterized by public key type `PK`,
secret key type `SK_kem`, ciphertext type `CT`, and shared secret type `SS`.

It provides three operations: `encaps` produces a ciphertext and shared secret from a public key,
`decaps` recovers the shared secret from a ciphertext using the secret key, and the built-in
`correctness` field guarantees that honest encaps/decaps round-trips successfully.

:::paragraph
```anchor KEMStructure
structure KEM (PK SK_kem CT SS : Type _) where
  encaps : PK → CT × SS
  decaps : SK_kem → CT → SS
  correctness : ∀ (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS),
    encaps pk = (ct, ss) → decaps sk ct = ss
```
:::

# Correctness theorem

:::theorem "kem_decaps_encaps" (parent := "kem_core") (tags := "kem, pq, correctness") (effort := "small") (priority := "high")
If encapsulation produces `(ct, ss)`, then decapsulation with the corresponding
secret key recovers `ss`.
:::

:::proof "kem_decaps_encaps"
This is exactly the `correctness` field of the KEM interface.
:::

{anchorTerm KEMDecapsEncaps}`KEM_decaps_encaps`: if encapsulation produces (ct, ss), then
decapsulation with the corresponding secret key recovers ss.

:::paragraph
```anchor KEMDecapsEncaps
theorem KEM_decaps_encaps {PK SK_kem CT SS : Type _} (kem : KEM PK SK_kem CT SS)
    (pk : PK) (sk : SK_kem) (ct : CT) (ss : SS)
    (h : kem.encaps pk = (ct, ss)) :
    kem.decaps sk ct = ss :=
  kem.correctness pk sk ct ss h
```
:::
