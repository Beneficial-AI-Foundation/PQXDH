import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Key Derivation Function" =>

A KDF deterministically derives a fixed-size key from variable-length
input material. In X3DH the input is the concatenation of the
DH outputs and the result is the session key SK.

Two formalizations coexist, modeling different aspects of the KDF.

# Deterministic KDF (for correctness proofs)

```
structure KDF (I K : Type _) where
  derive : I → K
```

Used in the correctness proofs (`X3DH_agree`, `X3DH_handshake_correct`),
which only need "same input → same output" — no randomness or
security assumptions.

# Random Oracle KDF (for security proofs)

```
abbrev KDFOracle (I K : Type) := I →ₒ K
```

An oracle `I →ₒ K` implemented by VCV-io's `randomOracle`
(lazy cached uniform sampling). Used in the security proofs
(passive message secrecy), where the KDF is modeled as a random
oracle per the paper's assumption 4 (§2.5).

The paper makes the same distinction: correctness is unconditional,
security assumes the ROM.
