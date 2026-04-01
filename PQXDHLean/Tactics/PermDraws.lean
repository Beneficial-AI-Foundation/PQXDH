/-
Tactic `perm_draws` for automatically proving distributional equivalences
between probability computations that differ only in the order of
independent uniform draws (and possibly unused draws).

After normalizing both sides to bind chains of uniform samples,
`perm_draws` closes the goal by:
1. Adding unused draws to the LHS if the RHS has more (via `probOutput_bind_const`)
2. Computing the draw permutation from de Bruijn index analysis
3. Emitting adjacent transpositions on the LHS (via `probEvent_bind_bind_swap`)

All rewrites target the LHS only (`conv_lhs`), so the RHS is never modified.
-/
import Lean
import VCVio.EvalDist.Monad.Basic

open Lean Elab Tactic Meta

namespace PQXDHLean.Tactics

-- ============================================================
-- Expression utilities
-- ============================================================

/-- Find an application of `name` anywhere in `e`. -/
private partial def findApp? (name : Name) (e : Expr) : Option Expr :=
  if e.getAppFn.isConstOf name then some e
  else match e with
    | .app f a => findApp? name f |>.orElse (fun _ => findApp? name a)
    | .lam _ t b _ => findApp? name t |>.orElse (fun _ => findApp? name b)
    | .forallE _ t b _ => findApp? name t |>.orElse (fun _ => findApp? name b)
    | .letE _ t v b _ =>
      findApp? name t |>.orElse (fun _ =>
        findApp? name v |>.orElse (fun _ => findApp? name b))
    | .mdata _ e => findApp? name e
    | _ => none

-- ============================================================
-- Goal parsing
-- ============================================================

/-- Extract the computation from a `probOutput comp z` expression.
    Returns `(comp, z)`. -/
private def matchProbOutput? (e : Expr) : Option (Expr × Expr) := do
  let app ← findApp? ``probOutput e
  let args := app.getAppArgs
  guard (args.size ≥ 2)
  some (args[args.size - 2]!, args[args.size - 1]!)

/-- Extract the computation from a `probEvent comp p` expression.
    Returns `(comp, p)`. -/
private def matchProbEvent? (e : Expr) : Option (Expr × Expr) := do
  let app ← findApp? ``probEvent e
  let args := app.getAppArgs
  guard (args.size ≥ 2)
  some (args[args.size - 2]!, args[args.size - 1]!)

/-- Parse goal `Pr[= z | lhs] = Pr[= z | rhs]`.
    Returns `(lhsComp, rhsComp, z)`. -/
private def parseProbEqSides (target : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let target ← instantiateMVars target
  let target := target.consumeMData
  unless target.isAppOfArity ``Eq 3 do return none
  let lhsExpr := target.getArg! 1
  let rhsExpr := target.getArg! 2
  -- Try probOutput first, then probEvent
  if let some (lhsComp, z) := matchProbOutput? lhsExpr then
    if let some (rhsComp, _) := matchProbOutput? rhsExpr then
      return some (lhsComp, rhsComp, z)
  if let some (lhsComp, z) := matchProbEvent? lhsExpr then
    if let some (rhsComp, _) := matchProbEvent? rhsExpr then
      return some (lhsComp, rhsComp, z)
  return none

-- ============================================================
-- Bind chain extraction
-- ============================================================

/-- Extract a right-associated bind chain from a computation expression.
    Returns `(draws, body)` where `draws[0]` is the outermost draw.
    The body has loose bvar references:
      bvar 0 = innermost (last) draw,
      bvar (n-1) = outermost (first) draw. -/
private partial def extractBindChain (e : Expr) :
    MetaM (Array Expr × Expr) := do
  let e ← whnfR e
  if e.getAppFn.isConstOf ``Bind.bind && e.getAppNumArgs ≥ 6 then
    let drawComp := e.getArg! 4
    let cont := e.getArg! 5
    match cont with
    | .lam _ _ body _ =>
      let (innerDraws, innerBody) ← extractBindChain body
      return (#[drawComp] ++ innerDraws, innerBody)
    | _ => return (#[], e)
  else
    return (#[], e)

-- ============================================================
-- De Bruijn analysis: match draws between LHS and RHS
-- ============================================================

/-- Parallel traversal of two expressions to collect `(bvar_L, bvar_R)` pairs
    at corresponding positions. Both expressions should be structurally
    identical except for bvar indices. -/
private partial def collectBVarPairs :
    Expr → Expr → Array (Nat × Nat) → Array (Nat × Nat)
  | .bvar i, .bvar j, acc => acc.push (i, j)
  | .app f₁ a₁, .app f₂ a₂, acc =>
    collectBVarPairs a₁ a₂ (collectBVarPairs f₁ f₂ acc)
  | .lam _ t₁ b₁ _, .lam _ t₂ b₂ _, acc =>
    collectBVarPairs b₁ b₂ (collectBVarPairs t₁ t₂ acc)
  | .forallE _ t₁ b₁ _, .forallE _ t₂ b₂ _, acc =>
    collectBVarPairs b₁ b₂ (collectBVarPairs t₁ t₂ acc)
  | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _, acc =>
    collectBVarPairs b₁ b₂ (collectBVarPairs v₁ v₂ (collectBVarPairs t₁ t₂ acc))
  | .mdata _ e₁, e₂, acc => collectBVarPairs e₁ e₂ acc
  | e₁, .mdata _ e₂, acc => collectBVarPairs e₁ e₂ acc
  | _, _, acc => acc

-- ============================================================
-- Permutation computation
-- ============================================================

/-- Given bvar pairs and draw counts, compute the permutation.
    `perm[lhsPos] = rhsPos` for each LHS draw position.
    Unused LHS draws (newly inserted) are mapped to unused RHS positions. -/
private def computePermutation (pairs : Array (Nat × Nat))
    (nL nR : Nat) : MetaM (Array Nat) := do
  let mut perm : Array (Option Nat) := Array.mk <| List.replicate nL none
  let mut usedRhs : Array Bool := Array.mk <| List.replicate nR false
  -- Map used draws by de Bruijn pairs
  for (bvarL, bvarR) in pairs do
    let lhsPos := nL - 1 - bvarL
    let rhsPos := nR - 1 - bvarR
    if lhsPos < nL && rhsPos < nR then
      if perm[lhsPos]! == none then
        perm := perm.set! lhsPos (some rhsPos)
        usedRhs := usedRhs.set! rhsPos true
  -- Collect unused RHS positions for inserted draws
  let mut unusedRhsPos : Array Nat := #[]
  for i in [:nR] do
    unless usedRhs[i]! do
      unusedRhsPos := unusedRhsPos.push i
  -- Fill unmapped LHS positions with unused RHS positions
  let mut result : Array Nat := Array.mk <| List.replicate nL 0
  let mut unusedIdx := 0
  for i in [:nL] do
    match perm[i]! with
    | some pos => result := result.set! i pos
    | none =>
      if unusedIdx < unusedRhsPos.size then
        result := result.set! i unusedRhsPos[unusedIdx]!
        unusedIdx := unusedIdx + 1
      else
        throwError "perm_draws: mismatch in unused draw count"
  return result

-- ============================================================
-- Bubble sort decomposition
-- ============================================================

/-- Decompose a permutation into adjacent transpositions via bubble sort.
    Input: `targetIndices[i]` = where element at position `i` should go.
    Output: sequence of depths (swap positions `depth` and `depth+1`). -/
private def bubbleSortSwaps (targetIndices : Array Nat) : Array Nat := Id.run do
  let mut arr := targetIndices
  let mut swaps : Array Nat := #[]
  let n := arr.size
  let mut changed := true
  while changed do
    changed := false
    for i in [:n - 1] do
      if arr[i]! > arr[i + 1]! then
        let tmp := arr[i]!
        arr := arr.set! i arr[i + 1]!
        arr := arr.set! (i + 1) tmp
        swaps := swaps.push i
        changed := true
  return swaps

-- ============================================================
-- Tactic emission
-- ============================================================

/-- Build proof term for swapping adjacent draws at given depth.
    Depth 0: `probEvent_bind_bind_swap _ _ _ _`
    Depth n+1: `probEvent_bind_congr fun _ _ => (inner)` -/
private def mkSwapProofTerm (depth : Nat) : TacticM (TSyntax `term) := do
  match depth with
  | 0 => `(term| probEvent_bind_bind_swap _ _ _ _)
  | n + 1 =>
    let inner ← mkSwapProofTerm n
    `(term| probEvent_bind_congr fun _ _ => $inner)

/-- Emit a single adjacent transposition at `depth`, targeting LHS only.
    Handles the `probOutput`↔`probEvent` conversion. -/
private def emitLhsSwap (depth : Nat) : TacticM Unit := do
  let proof ← mkSwapProofTerm depth
  -- Try with probEvent conversion first
  try
    evalTactic (← `(tactic|
      (simp only [← probEvent_eq_eq_probOutput]
       conv_lhs => rw [show _ from $proof]
       try simp only [probEvent_eq_eq_probOutput])))
    return
  catch _ => pure ()
  -- Fallback: try direct rewrite
  try
    evalTactic (← `(tactic| conv_lhs => rw [show _ from $proof]))
    return
  catch _ => pure ()
  throwError "perm_draws: failed to emit swap at depth {depth}"

/-- Insert one unused draw at position 0 in LHS.
    `sampleExpr` is the draw computation to prepend (e.g., `$ᵗ F`).
    `z` is the output value from the `Pr[= z | ...]` goal. -/
private def emitInsertUnusedDraw (sampleExpr z : Expr) : TacticM Unit := do
  let sampleSyn ← PrettyPrinter.delab sampleExpr
  let zSyn ← PrettyPrinter.delab z
  try
    evalTactic (← `(tactic|
      conv_lhs =>
        rw [(by simp [probOutput_bind_const] :
          ∀ body, probOutput body $zSyn =
            probOutput ($sampleSyn >>= fun _ => body) $zSyn)]))
    return
  catch _ => pure ()
  throwError "perm_draws: failed to insert unused draw (sample = {sampleExpr})"

-- ============================================================
-- Main tactic
-- ============================================================

set_option linter.style.emptyLine false in
/-- `perm_draws` automatically proves probability equality goals of the form
    `Pr[= z | LHS] = Pr[= z | RHS]` where both sides are sequences of
    independent uniform draws followed by the same body expression,
    possibly differing in draw order and unused draws.

    All rewrites target the LHS only (via `conv_lhs`). -/
elab "perm_draws" : tactic => withMainContext do
  let target ← getMainTarget
  let some (lhsComp, rhsComp, z) ← parseProbEqSides target
    | throwError "perm_draws: goal is not of the form Pr[... | LHS] = Pr[... | RHS]"

  -- Extract bind chains
  let (lhsDraws, _lhsBody) ← extractBindChain lhsComp
  let (rhsDraws, rhsBody) ← extractBindChain rhsComp
  let nL := lhsDraws.size
  let nR := rhsDraws.size

  logInfo m!"perm_draws: LHS has {nL} draws, RHS has {nR} draws"

  -- Insert unused draws if LHS has fewer (use first RHS draw as sample template)
  if nR > nL then
    logInfo m!"perm_draws: inserting {nR - nL} unused draw(s) into LHS"
    let sampleExpr := rhsDraws[0]!
    for _ in [:nR - nL] do
      emitInsertUnusedDraw sampleExpr z

  -- Re-extract after possible inserts
  let target' ← getMainTarget
  let some (lhsComp', _, _) ← parseProbEqSides target'
    | throwError "perm_draws: goal changed unexpectedly after inserting draws"
  let (lhsDraws', lhsBody') ← extractBindChain lhsComp'
  let nL' := lhsDraws'.size

  guard (nL' == nR) <|>
    throwError "perm_draws: draw count mismatch after inserts: LHS={nL'}, RHS={nR}"

  -- Match draws by de Bruijn index analysis
  let pairs := collectBVarPairs lhsBody' rhsBody #[]

  -- Compute permutation
  let perm ← computePermutation pairs nL' nR

  logInfo m!"perm_draws: permutation = {perm.toList}"

  -- Decompose into adjacent swaps
  let swaps := bubbleSortSwaps perm

  if swaps.size == 0 then
    logInfo m!"perm_draws: draws already in correct order"
  else
    logInfo m!"perm_draws: {swaps.size} swap(s): {swaps.toList}"

  -- Emit swaps
  for depth in swaps do
    emitLhsSwap depth

  logInfo m!"perm_draws: done"

end PQXDHLean.Tactics
