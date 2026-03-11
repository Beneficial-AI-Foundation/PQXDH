/-
Abstract Key Derivation Function (KDF).

A KDF deterministically derives a fixed-size key from variable-length
input material. In X3DH/PQXDH the input is the concatenation of the
DH outputs and the result is the session key SK.

## Security assumptions (§2.5, assumption 2)

The concrete instantiation is HKDF (RFC 5869) with SHA-256.
The paper assumes the KDF behaves as a random oracle: its output is
indistinguishable from a uniformly random key.

## Abstract interface

We model a KDF as a single deterministic `derive` function with a
correctness axiom that equal inputs yield equal outputs (which is
trivially true for any function, but makes the structure explicit
for downstream composition proofs).

Reference: Bhargavan et al., §2.1 and §2.5 assumption (2).
-/

import Mathlib.Tactic.TypeStar

/-! ## KDF structure -/

/-- Abstract Key Derivation Function.

    Parameterized by:
    - `I`: input type (e.g. concatenation of DH outputs)
    - `K`: key type (derived session key)

    Operations:
    - `derive`: deterministically map input material to a key -/
structure KDF (I K : Type*) where
  /-- Derive a key from input material. -/
  derive : I → K
