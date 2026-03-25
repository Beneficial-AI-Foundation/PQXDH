import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.DH
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

:::group "dh_properties"
Core algebraic properties of DH.
:::

Abstract Diffie-Hellman over any additive commutative group.

We define DH(a, B) = \[a\]B as scalar multiplication in an `AddCommGroup`.
All algebraic properties (commutativity, associativity, distributivity)
follow from the group axioms alone — no curve, field, or encoding is
mentioned. Protocol proofs (X3DH, PQXDH) import only this file.

# Definition

:::definition "DH" (lean := "DH") (parent := "dh")
`DH` is defined as scalar multiplication `a • B` in an additive commutative group.
:::

# Core properties

:::theorem "DH-comm" (lean := "DH_comm") (parent := "dh_properties")
DH is commutative — DH(a, DH(b, P)) = DH(b, DH(a, P)).
This is the key property that makes X3DH work: Alice and Bob compute the same shared secrets.
:::

:::proof "DH-comm"
By commutativity of natural number multiplication and the `mul_nsmul'` lemma.

```
simp only [DH, ← mul_nsmul', Nat.mul_comm]
```
:::

:::theorem "DH-assoc" (lean := "DH_assoc") (parent := "dh_properties")
DH is associative — `DH(a, DH(b, B)) = DH(a * b, B)`.
:::

:::proof "DH-assoc"
By the `mul_nsmul'` lemma.

```
simp only [DH, ← mul_nsmul']
```
:::

:::theorem "DH-zero" (lean := "DH_zero") (parent := "dh_properties")
Scalar zero yields the identity element.
:::

:::proof "DH-zero"
```
exact zero_nsmul B
```
:::

:::theorem "DH-one" (lean := "DH_one") (parent := "dh_properties")
Scalar one is the identity operation.
:::

:::proof "DH-one"
```
exact one_nsmul B
```
:::

:::theorem "DH-add" (lean := "DH_add") (parent := "dh_properties")
DH distributes over scalar addition.
:::

:::proof "DH-add"
```
exact add_nsmul B a b
```
:::
