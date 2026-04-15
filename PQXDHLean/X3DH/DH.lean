/-
Diffie-Hellman as scalar multiplication over `[Field F] [Module F G]`.

`DH a B` is an `abbrev` for `a • B`, so all Mathlib `Module` lemmas
(`mul_smul`, `add_smul`, `one_smul`, …) apply directly.

## Notation

| Textbook (multiplicative) | This file (additive)             |
|---------------------------|----------------------------------|
| `gᵃ`                     | `a • G₀`                         |
| `(gᵃ)ᵇ = gᵃᵇ`            | `b • (a • G₀) = (b * a) • G₀`    |
| `gᵃ · gᵇ = gᵃ⁺ᵇ`         | `a • G₀ + b • G₀ = (a+b) • G₀`   |
-/
import Mathlib.Algebra.Module.Basic

variable {F : Type _} [Field F]
variable {G : Type _} [AddCommGroup G] [Module F G]

/-- Diffie-Hellman function: DH(a, B) = a • B. -/
abbrev DH (a : F) (B : G) : G := a • B
