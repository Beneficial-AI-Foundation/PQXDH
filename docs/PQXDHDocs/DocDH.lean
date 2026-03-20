import VersoManual
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject "."
set_option verso.exampleModule "PQXDHLean.DH"

#doc (Manual) "Diffie-Hellman" =>
%%%
tag := "dh"
%%%

Abstract Diffie-Hellman over any additive commutative group.

We define DH(a, B) = \[a\]B as scalar multiplication in an `AddCommGroup`.
All algebraic properties (commutativity, associativity, distributivity)
follow from the group axioms alone — no curve, field, or encoding is
mentioned. Protocol proofs (X3DH, PQXDH) import only this file.

# Definition

{anchorTerm DHDef}`DH` is defined as scalar multiplication `a • B` in an additive commutative group:

:::paragraph
```anchor DHDef
noncomputable def DH (a : ℕ) (B : G) : G := a • B
```
:::

# Core properties

{anchorTerm DHComm}`DH_comm`: DH is commutative — DH(a, DH(b, P)) = DH(b, DH(a, P)).
This is the key property that makes X3DH work: Alice and Bob compute the same shared secrets.

:::paragraph
```anchor DHComm
theorem DH_comm (a b : ℕ) (P : G) :
    DH a (DH b P) = DH b (DH a P) := by
  simp only [DH, ← mul_nsmul', Nat.mul_comm]
```
:::

{anchorTerm DHAssoc}`DH_assoc`: DH is associative — `DH(a, DH(b, B)) = DH(a * b, B)`.

:::paragraph
```anchor DHAssoc
theorem DH_assoc (a b : ℕ) (B : G) :
    DH a (DH b B) = DH (a * b) B := by
  simp only [DH, ← mul_nsmul']
```
:::

{anchorTerm DHZero}`DH_zero`: scalar zero yields the identity element.

:::paragraph
```anchor DHZero
theorem DH_zero (B : G) : DH 0 B = (0 : G) := by
  exact zero_nsmul B
```
:::

{anchorTerm DHOne}`DH_one`: scalar one is the identity operation.

:::paragraph
```anchor DHOne
theorem DH_one (B : G) : DH 1 B = B := by
  exact one_nsmul B
```
:::

{anchorTerm DHAdd}`DH_add`: DH distributes over scalar addition.

:::paragraph
```anchor DHAdd
theorem DH_add (a b : ℕ) (B : G) :
    DH (a + b) B = DH a B + DH b B := by
  exact add_nsmul B a b
```
:::
