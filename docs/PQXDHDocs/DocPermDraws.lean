import VersoManual
import VersoBlueprint
import PQXDHLean.Tactics.PermDraws

open Verso.Genre Manual
open Informal


#doc (Manual) "The PermDraws Tactic" =>
%%%
tag := "perm_draws"
%%%

:::group "perm_draws_core"
Custom tactic for automatic distributional equivalence proofs.
:::

:::definition "perm_draws_tactic" (lean := "PQXDHLean.Tactics.permDrawsImpl") (parent := "perm_draws_core")
A custom Lean 4 tactic for automatically proving distributional
equivalences between probability computations that differ only in
the order of independent uniform draws. Invoked as `perm_draws`
in tactic mode.
:::

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
a single call to `perm_draws` closes the goal.

The tactic is used in the distributional equivalence proofs that
underpin the passive secrecy theorem.

# Design decision

All rewrites target the LHS only via `conv_lhs`. This avoids the
unpredictability of VCV-io's rewrite tactics, which use
`first | conv_lhs | conv_rhs` and can modify either side of the
equation when both sides have matching structure.

# Scope

The tactic handles goals where all draws are independent uniform
samples, the bodies are identical modulo variable permutation, and
the only structural difference is draw order and unused draws.

It does not handle dependent draws, conditional branches, different
body structures, or computational indistinguishability arguments.

# Implementation

The tactic is implemented in six modules, each handling a distinct
phase of the proof automation pipeline.

## Expression utilities

:::definition "perm_draws_findApp" (lean := "PQXDHLean.Tactics.findApp?") (parent := "perm_draws_core")
Search for an application of a given constant anywhere inside an
expression tree, used by the goal parser to locate `probOutput`
and `probEvent` subexpressions.
:::

## Goal parsing

:::definition "perm_draws_matchProbOutput" (lean := "PQXDHLean.Tactics.matchProbOutput?") (parent := "perm_draws_core")
Extract the computation from a `probOutput comp z` expression.
:::

:::definition "perm_draws_matchProbEvent" (lean := "PQXDHLean.Tactics.matchProbEvent?") (parent := "perm_draws_core")
Extract the computation from a `probEvent comp p` expression.
:::

:::definition "perm_draws_parseProbEqSides" (lean := "PQXDHLean.Tactics.parseProbEqSides") (parent := "perm_draws_core")
Parse the goal `Pr[= z | LHS] = Pr[= z | RHS]`, supporting both
`probOutput` and `probEvent` variants.
:::

## Bind chain extraction

:::definition "perm_draws_extractBindChain" (lean := "PQXDHLean.Tactics.extractBindChain") (parent := "perm_draws_core")
Walk a computation's right-associated bind chain, collecting the
sequence of draw computations and the residual body expression.
The body has loose bound variable references where `bvar 0` is the
innermost (last) draw and `bvar (n-1)` is the outermost (first) draw.
:::

## De Bruijn analysis

:::definition "perm_draws_collectBVarPairs" (lean := "PQXDHLean.Tactics.collectBVarPairs") (parent := "perm_draws_core")
Traverse the LHS and RHS bodies in parallel, collecting pairs of
de Bruijn indices at corresponding positions. Each pair (i, j) means
LHS draw i fills the same role as RHS draw j. Draws that appear
in one body but not the other are classified as unused.
:::

## Permutation computation and bubble sort

:::definition "perm_draws_computePermutation" (lean := "PQXDHLean.Tactics.computePermutation") (parent := "perm_draws_core")
Given bvar pairs and draw counts, compute the permutation mapping
each LHS draw position to the corresponding RHS position. Unused
LHS draws (newly inserted) are mapped to unused RHS positions.
:::

:::definition "perm_draws_bubbleSortSwaps" (lean := "PQXDHLean.Tactics.bubbleSortSwaps") (parent := "perm_draws_core")
Decompose a permutation into adjacent transpositions via bubble sort,
producing a minimal swap sequence.
:::

## Tactic emission

:::definition "perm_draws_mkSwapProofTerm" (lean := "PQXDHLean.Tactics.mkSwapProofTerm") (parent := "perm_draws_core")
Build proof term for swapping adjacent draws at given depth.
Depth 0 uses `probEvent_bind_bind_swap`, depth n+1 wraps in
`probEvent_bind_congr`.
:::

:::definition "perm_draws_emitLhsSwap" (lean := "PQXDHLean.Tactics.emitLhsSwap") (parent := "perm_draws_core")
Emit a single adjacent transposition at a given depth, targeting
LHS only. Handles the `probOutput` to `probEvent` conversion.
:::

:::definition "perm_draws_emitInsertUnusedDraw" (lean := "PQXDHLean.Tactics.emitInsertUnusedDraw") (parent := "perm_draws_core")
Insert one unused draw at position 0 in LHS via
`probOutput_bind_const`.
:::
