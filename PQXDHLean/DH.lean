/-
Abstract Diffie-Hellman over any additive commutative group.

Defines DH(a, B) = [a]·B as scalar multiplication in an `AddCommGroup`.
All algebraic properties (commutativity, associativity, distributivity)
follow from the group axioms alone — no curve, field, or encoding is
mentioned.

Protocol proofs (X3DH, PQXDH) import only this file.
-/
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Order.Ring.Nat

variable {G : Type _} [AddCommGroup G]

/-- §2.1, p. 470: Diffie-Hellman function DH(a, B) = [a]·B.
Scalar multiplication of a natural number `a` by a group element `B`.
The concrete instantiation is X25519 (Curve25519).
See "Session Secret Generation" paragraph: DHᵢ = (Kᵖᵏ)^{K'ˢᵏ}. -/
noncomputable def DH (a : ℕ) (B : G) : G := a • B

/-! ## Core properties -/

/-- §2.1, p. 470: DH commutativity — DH(a, DH(b, P)) = DH(b, DH(a, P)).
This is the fundamental property enabling X3DH/PQXDH: Alice and Bob
compute the same shared secrets despite using different private keys.
Used in "Completing the Handshake": "Blake performs the symmetric DH
computations, mutatis mutandis". -/
theorem DH_comm (a b : ℕ) (P : G) :
    DH a (DH b P) = DH b (DH a P) := by
  simp only [DH, ← mul_nsmul', Nat.mul_comm]

/-- §2.1, p. 470: DH associativity — DH(a, DH(b, B)) = DH(a * b, B).
Iterated scalar multiplication reduces to a single multiplication. -/
theorem DH_assoc (a b : ℕ) (B : G) :
    DH a (DH b B) = DH (a * b) B := by
  simp only [DH, ← mul_nsmul']

/-- Algebraic property: scalar zero yields the group identity element. -/
theorem DH_zero (B : G) : DH 0 B = (0 : G) := by
  exact zero_nsmul B

/-- Algebraic property: scalar one is the identity operation on group elements. -/
theorem DH_one (B : G) : DH 1 B = B := by
  exact one_nsmul B

/-- Algebraic property: DH distributes over scalar addition,
DH(a + b, B) = DH(a, B) + DH(b, B). -/
theorem DH_add (a b : ℕ) (B : G) :
    DH (a + b) B = DH a B + DH b B := by
  exact add_nsmul B a b
