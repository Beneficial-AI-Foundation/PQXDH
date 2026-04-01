import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Diffie-Hellman" =>

Abstract Diffie-Hellman as scalar multiplication over `[Field F] [Module F G]`.

`DH a B` is an `abbrev` for `a • B` (Mathlib's `Module` scalar multiplication),
so all `Module` lemmas apply directly without unfolding.

*Definition*

```
abbrev DH (a : F) (B : G) : G := a • B
```

Declared `abbrev` so it is definitionally equal to scalar multiplication.

*Notation*

| Textbook (multiplicative) | This file (additive)            |
|---------------------------|---------------------------------|
| `g^a`                     | `a • G₀`                       |
| `(g^a)^b = g^{ab}`       | `b • (a • G₀) = (b * a) • G₀` |
| `g^a · g^b = g^{a+b}`    | `a • G₀ + b • G₀ = (a+b) • G₀`|

*Algebraic properties*

Because `DH` is an `abbrev`, these properties follow directly from the `Module F G` API:

- *Commutativity*: `DH(a, DH(b, P)) = DH(b, DH(a, P))` — via `smul_smul` + `mul_comm`
- *Associativity*: `DH(a, DH(b, B)) = DH(a * b, B)` — via `mul_smul`
- *Zero*: `DH(0, B) = 0` — via `zero_smul`
- *One*: `DH(1, B) = B` — via `one_smul`
- *Addition*: `DH(a + b, B) = DH(a, B) + DH(b, B)` — via `add_smul`
