/-
Abstract Diffie-Hellman over any additive commutative group.

Defines DH(a, B) = [a]B as scalar multiplication in an `AddCommGroup`.
All algebraic properties (commutativity, associativity, distributivity)
follow from the group axioms alone — no curve, field, or encoding is
mentioned.

Protocol proofs (X3DH, PQXDH) import only this file.
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Order.Ring.Nat

variable {G : Type _} [AddCommGroup G]

/-- Abstract Diffie-Hellman: DH(a, B) = [a]B in an additive commutative group. -/
noncomputable def DH (a : ℕ) (B : G) : G := a • B

/-! ## Core properties -/

theorem DH_comm (a b : ℕ) (P : G) :
    DH a (DH b P) = DH b (DH a P) := by
  simp only [DH, ← mul_nsmul', Nat.mul_comm]

theorem DH_assoc (a b : ℕ) (B : G) :
    DH a (DH b B) = DH (a * b) B := by
  simp only [DH, ← mul_nsmul']

theorem DH_zero (B : G) : DH 0 B = (0 : G) := by
  exact zero_nsmul B

theorem DH_one (B : G) : DH 1 B = B := by
  exact one_nsmul B

theorem DH_add (a b : ℕ) (B : G) :
    DH (a + b) B = DH a B + DH b B := by
  exact add_nsmul B a b
