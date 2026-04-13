import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.DH

open Verso.Genre Manual
open Informal


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

The formalization uses additive group notation following the Mathlib
convention, instead of the multiplicative notation from textbooks:

- `g^a` becomes `a • G₀` (scalar multiplication)
- `(g^a)^b = g^{ab}` becomes `b • (a • G₀) = (b * a) • G₀`
- `g^a * g^b = g^{a+b}` becomes `a • G₀ + b • G₀ = (a + b) • G₀`

# Algebraic properties

Because `DH` is declared as an `abbrev`, it is definitionally equal
to Mathlib's scalar multiplication `a • B`. All algebraic properties
are inherited directly from the `Module F G` typeclass API in Mathlib
(`Mathlib.Algebra.Module.Basic`), with no additional proofs needed:

- *Commutativity*: `DH a (DH b P) = DH b (DH a P)` from `smul_smul` + `mul_comm` (Mathlib)
- *Associativity*: `DH a (DH b B) = DH (a * b) B` from `mul_smul` (Mathlib)
- *Zero*: `DH 0 B = 0` from `zero_smul` (Mathlib)
- *One*: `DH 1 B = B` from `one_smul` (Mathlib)
- *Addition*: `DH (a + b) B = DH a B + DH b B` from `add_smul` (Mathlib)
