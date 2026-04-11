import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.DH

open Verso.Genre Manual
open Informal

set_option verso.exampleProject ".."
set_option verso.exampleModule "PQXDHLean.X3DH.DH"

#doc (Manual) "Diffie-Hellman" =>
%%%
tag := "dh"
%%%

:::group "dh_core"
Core algebraic interface for abstract Diffie-Hellman.
:::

Abstract Diffie-Hellman over any additive commutative group.
We define DH(a, B) as scalar multiplication in a `Module F G`,
where `F` is a field and `G` is an additive commutative group.
All algebraic properties (commutativity, associativity, distributivity)
follow from the module axioms alone, with no curve, field, or encoding
mentioned. Protocol proofs (X3DH, PQXDH) import only this file.

# Definition

:::definition "dh_spec" (lean := "DH") (parent := "dh_core")
Abstract Diffie-Hellman is modeled as scalar multiplication
in a module over a field. `DH a B` is an `abbrev` for `a * B`
(Mathlib's `Module` scalar action), so all `Module` lemmas
apply directly without unfolding.
:::

# Notation

The formalization uses additive group notation (Mathlib convention)
instead of the multiplicative notation from textbooks.
For example, `g^a` becomes `a * G₀`, and `(g^a)^b = g^(ab)` becomes
`b * (a * G₀) = (b * a) * G₀`.

# Algebraic properties

Because DH is an `abbrev`, these properties follow directly from the `Module F G` API:
commutativity via `smul_smul` + `mul_comm`,
associativity via `mul_smul`,
zero via `zero_smul`,
one via `one_smul`,
and addition via `add_smul`.
