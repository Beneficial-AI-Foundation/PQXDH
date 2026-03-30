import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.DH
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Diffie-Hellman" =>

:::group "dh"
Diffie-Hellman
:::

Abstract Diffie-Hellman as scalar multiplication over `[Field F] [Module F G]`.

`DH a B` is an `abbrev` for `a • B` (Mathlib's `Module` scalar multiplication),
so all `Module` lemmas apply directly without unfolding.

# Definition

:::definition "DH" (lean := "DH") (parent := "dh")
`DH(a, B) = a • B`. Declared `abbrev` so it is definitionally equal to scalar multiplication.
:::

# Algebraic properties

Because `DH` is an `abbrev`, these properties are not declared as
separate theorems — they follow directly from the `Module F G` API:

- **Commutativity**: `DH(a, DH(b, P)) = DH(b, DH(a, P))` — via `smul_smul` + `mul_comm`
- **Associativity**: `DH(a, DH(b, B)) = DH(a * b, B)` — via `mul_smul`
- **Zero**: `DH(0, B) = 0` — via `zero_smul`
- **One**: `DH(1, B) = B` — via `one_smul`
- **Addition**: `DH(a + b, B) = DH(a, B) + DH(b, B)` — via `add_smul`
