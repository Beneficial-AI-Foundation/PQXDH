import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "The PermDraws Tactic" =>

A custom Lean 4 tactic for automatically proving distributional
equivalences between probability computations that differ only in
the order of independent uniform draws.

# Motivation

In game-based cryptographic proofs, security reductions often
require showing that two probabilistic computations produce the
same distribution. After unfolding definitions and simplifying
oracle implementations, these goals reduce to: both sides sample
the same uniform draws but in different order, possibly with
extra unused draws on one side. Proving this by hand requires
computing the permutation between draw orders and emitting a
sequence of adjacent transpositions, which is tedious and error-prone.

The `perm_draws` tactic automates this entirely.

# Usage

After normalizing both sides of a distributional equality to
bind chains of uniform draws (typically via `simp` and `simp_all`),
a single call to `perm_draws` closes the goal:

```
private lemma passiveReal_eq_ddhExpReal
    (g : G) (adv : PassiveAdversary G SK) :
    evalDist (execGame (passiveReal g adv)) =
    evalDist (DiffieHellman.ddhExpReal g (ddhReduction adv)) := by
  unfold passiveReal passiveGame DiffieHellman.ddhExpReal ddhReduction execGame
  simp only [simulateQ_bind, simulateQ_query, ...]
  ext z; change Pr[= z | _] = Pr[= z | _]; simp_all
  perm_draws
```

# Algorithm

The tactic operates in five phases:

## Goal parsing

Extract the computations from a goal of the form
`Pr[= z | LHS] = Pr[= z | RHS]` (or the `probEvent` variant).

## Bind chain extraction

Walk each computation's right-associated bind chain, collecting the
sequence of draw computations and the residual body expression.

## Draw matching

Traverse the LHS and RHS bodies in parallel, collecting pairs of
de Bruijn indices at corresponding positions. Each pair `(i, j)`
means "LHS draw `i` fills the same role as RHS draw `j`." Draws
that appear in one body but not the other are classified as unused.

## Unused draw insertion

If the RHS has more draws than the LHS (e.g., the DDH random
experiment samples an extra scalar `c` that does not appear in
the body), the tactic inserts matching unused draws at position 0
in the LHS using `probOutput_bind_const`.

## Permutation and swap emission

The draw correspondence defines a permutation. The tactic decomposes
it into adjacent transpositions via bubble sort, then emits one
`conv_lhs` rewrite per swap using `probEvent_bind_bind_swap` (with
`probEvent_bind_congr` for nested swaps).

# Design decision

All rewrites target the LHS only via `conv_lhs`. This avoids the
unpredictability of VCV-io's `vcstep rw under N`, which uses
`first | conv_lhs | conv_rhs` and can modify either side of the
equation when both sides have matching structure.

# Scope

The tactic handles goals where all draws are independent uniform
samples, the bodies are identical modulo variable permutation, and
the only structural difference is draw order and unused draws.

It does not handle dependent draws, conditional branches, different
body structures, or computational indistinguishability arguments.
