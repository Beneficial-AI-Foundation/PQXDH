/-
Abstract Diffie-Hellman over a module `Module F G`.

## Why `Module F G`

Modeling DH as `a • B` over `[Field F] [AddCommGroup G] [Module F G]`
gives two advantages:

  - Private keys live in a *field* `F`, which can be finite (e.g.
    `ZMod q`). This is necessary for sampling keys uniformly in
    security games.
  - Mathlib's `Module` typeclass provides a rich algebraic API
    (`mul_smul`, `add_smul`, `one_smul`, `zero_smul`, …).

## Notation

We use additive / EC-style notation:

| Textbook (multiplicative) | This file (additive)            |
|---------------------------|---------------------------------|
| `g^a`                     | `a • G₀`                        |
| `(g^a)^b = g^{ab}`        | `b • (a • G₀) = (b * a) • G₀`   |
| `g^a · g^b = g^{a+b}`     | `a • G₀ + b • G₀ = (a+b) • G₀`  |

Here `F` is the scalar field (e.g. `ZMod q` for a prime-order group),
`G` is the additive group of curve points, and `G₀ : G` is a generator.

## `DH` is an `abbrev`

`DH a B` is definitionally equal to `a • B`. This means all `Module`
and Mathlib lemmas apply directly — no unfolding needed. The algebraic
properties listed below are therefore redundant (each is a one-liner
via `simp`) but are kept as comments for documentation.
-/
import Mathlib.Algebra.Module.Basic

variable {F : Type _} [Field F]
variable {G : Type _} [AddCommGroup G] [Module F G]

/-- Diffie-Hellman function: DH(a, B) = a • B. -/
abbrev DH (a : F) (B : G) : G := a • B

/-! ## Algebraic properties (documentation only)

Each property follows from the `Module` API by `simp`.

Commutativity — DH(a, DH(b, P)) = DH(b, DH(a, P)).
   The fundamental property enabling key agreement: both parties
   compute the same shared secret despite using different private keys.
   Mathlib: `smul_smul` + `mul_comm`

   example (a b : F) (P : G) : DH a (DH b P) = DH b (DH a P) := by
     simp [mul_smul, mul_comm]

Associativity — DH(a, DH(b, B)) = DH(a * b, B).
   Mathlib: `mul_smul`

   example (a b : F) (B : G) : DH a (DH b B) = DH (a * b) B := by
     simp [mul_smul]

Zero — DH(0, B) = 0.           Mathlib: `zero_smul`
One  — DH(1, B) = B.           Mathlib: `one_smul`
Add  — DH(a+b, B) = DH(a,B) + DH(b,B).  Mathlib: `add_smul`
-/
