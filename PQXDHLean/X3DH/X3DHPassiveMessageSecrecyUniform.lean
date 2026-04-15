/-
Passive message secrecy for X3DH under the Random Oracle Model.

## Goal

Formalize the simplest meaningful security property of X3DH:
a passive eavesdropper who observes only public values cannot
distinguish the session key from a random key.

## The game

  1. Sample all private keys uniformly from F.
  2. Compute public keys and the four DH values via X3DH.
  3. Query the KDF oracle (random oracle) on the DH tuple to get
     the real session key.
  4. Sample a random key.
  5. Flip a bit b; give the adversary the public transcript
     and either the real key (b = true) or the random key.
  6. The adversary outputs a guess b'.
  7. Returns (b == b').

Security means: for all efficient adversaries, the probability
of returning true is negligibly close to 1/2.

## Random Oracle Model

The KDF is modeled as a random oracle using VCV-io's `→ₒ` oracle
spec and `randomOracle` implementation. The game has oracle access
to `(G × G × G × G) →ₒ SK`: on first query for input `x`, the
oracle samples `$ᵗ SK` uniformly and caches the result. Same input
always returns the same output.

The PQXDH specification (Section 4) states that the security
analysis models "the hash function as a random oracle." In the
ROM, the random oracle is a public function: all parties,
including the adversary, can query it. This justifies giving
the passive adversary oracle access to the KDF
(`OracleComp (KDFOracle ...) Bool`).

## Known limitation: `execGame` uses `uniformSampleImpl`

`execGame` currently implements the KDF via `uniformSampleImpl`,
which returns a fresh uniform sample on every query, ignoring
the input. This strips ROM consistency (same input → same output),
collapsing the real/random distinction: both games give the
adversary an independent uniform session key. The passive secrecy
advantage is therefore 0 for all adversaries, and the theorem
`passive_secrecy_le_ddh` is vacuously true (`0 ≤ |...|`).

A meaningful security statement requires replacing
`uniformSampleImpl` with VCVio's `randomOracle` in `execGame`.
With a proper ROM, the proof requires game-hopping and an
identical-until-bad argument (the bad event being the adversary
querying ROM on the DH tuple), which is where DDH does real work.
VCVio's ROM game-hopping infrastructure is still under development
(cf. BR93 example).

## VCV-io notation

- `$ᵗ F`: sample uniformly from finite type `F` (`SampleableType`)
- `→ₒ`: singleton oracle spec (`I →ₒ O` = oracle with input I, output O)
- `query x`: query the oracle on input `x`
- `ProbComp`: `OracleComp unifSpec` (pure probabilistic computation)
- `randomOracle`: lazy cached uniform sampling (`QueryImpl`)
- `simulateQ`: substitute oracle queries with an implementation

Reference: Bhargavan et al., USENIX Security 2024.
  The passive case is implicit in Theorem 2 (§5.2), which proves
  the stronger active-adversary (AKE game) version.
-/
import PQXDHLean.Tactics.PermDraws
import PQXDHLean.X3DH.X3DH
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.SimSemantics.Append
import VCVio.ProgramLogic.Tactics

open OracleComp OracleSpec

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {SK : Type} [Fintype SK] [DecidableEq SK] [SampleableType SK]

/-! ## Passive adversary

A passive adversary sees the public transcript and a candidate
session key. It has access to the KDF oracle (ROM) and outputs
a `Bool` guess: true = "real key", false = "random key". -/

/-- A passive X3DH adversary with ROM access. -/
abbrev PassiveAdversary (G SK : Type) :=
  G → G → G → G → G → SK → OracleComp (KDFOracle (G × G × G × G) SK) Bool

/-! ## Passive secrecy games (two-game formulation)

Instead of a single game with a hidden coin flip, we define two
games — real and random — and measure the adversary's ability to
distinguish between them:

- **Real game**: adversary receives the actual session key (from ROM)
- **Random game**: adversary receives a uniformly random key

The advantage is `|Pr[true | real] - Pr[true | rand]|`. -/

/-- Common game structure: sample keys, compute public values and
DH tuple, obtain a session key via `getSK`, and pass it to the
adversary. The real and random games differ only in `getSK`:
  - Real: `getSK` queries the ROM on the DH tuple
  - Random: `getSK` samples uniformly, ignoring the DH tuple -/
private def passiveGame
    (g : G)
    (adv : PassiveAdversary G SK)
    (getSK : (G × G × G × G) →
             OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
  let ikₐ ← $ᵗ F; let ekₐ ← $ᵗ F
  let ikᵦ ← $ᵗ F; let spkᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
  let IKₐ := ikₐ • g; let EKₐ := ekₐ • g
  let IKᵦ := ikᵦ • g; let SPKᵦ := spkᵦ • g; let OPKᵦ := opkᵦ • g
  let dh := X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ (some OPKᵦ)
  let sk ← getSK dh
  adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk

/-- Real game: session key from ROM applied to the X3DH DH tuple. -/
def passiveReal
    (g : G)
    (adv : PassiveAdversary G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool :=
  passiveGame (F := F) g adv fun dh =>
    query (spec := unifSpec + KDFOracle (G × G × G × G) SK) (Sum.inr dh)

/-- Random game: session key sampled uniformly at random. -/
def passiveRand
    (g : G)
    (adv : PassiveAdversary G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool :=
  passiveGame (F := F) g adv fun _ => $ᵗ SK

/-! ## Executing the games

To compute probabilities, the KDF oracle must be implemented.

**TODO: replace `uniformSampleImpl` with `randomOracle`.**

Currently, `execGame` uses `uniformSampleImpl` — each oracle query
returns a fresh uniform sample `$ᵗ SK`, ignoring the input. This
strips ROM consistency (same input → same output). Because the
adversary's KDF queries also return independent fresh samples,
the real and random games become distributionally identical:
in both, `sk` is an independent uniform draw. The passive secrecy
advantage is 0 for all adversaries, making `passive_secrecy_le_ddh`
vacuously true.

The correct implementation uses VCVio's `randomOracle` (lazy cached
uniform sampling), following the pattern in `BR93.lean`:
  `(simulateQ (idImpl + randomOracle) comp).run' ∅`
This preserves ROM consistency and makes the security statement
meaningful: the DDH reduction must then argue (via game-hopping
and an identical-until-bad bound) that the adversary cannot query
ROM on the DH tuple. -/

/-- Execute an oracle computation implementing the KDF as
fresh uniform samples.

**Caveat:** This uses `uniformSampleImpl`, not `randomOracle`.
See the module docstring for why this makes the security theorem
vacuous and the planned fix. -/
noncomputable def execGame
    (comp : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool) :
    ProbComp Bool :=
  let kdfImpl : QueryImpl (KDFOracle (G × G × G × G) SK) ProbComp :=
    fun _ => $ᵗ SK
  let idImpl : QueryImpl unifSpec ProbComp := QueryImpl.ofLift unifSpec ProbComp
  simulateQ (idImpl + kdfImpl) comp

/-! ## Advantage (two-game formulation)

Given two `ProbComp Bool` games `p` (real) and `q` (random),
`ProbComp.boolDistAdvantage p q = |Pr[true | p] - Pr[true | q]|`.

This measures how much the adversary's behavior changes between
the two games:
  - Advantage = 0 means the adversary cannot distinguish them.
  - Advantage = 1 means the adversary always tells them apart.

This is the standard cryptographic definition of distinguishing
advantage. It avoids the factor-of-2 issue that arises in the
single-game formulation (where a hidden coin flip selects between
real and random within one experiment). -/

/-- Passive secrecy advantage under the ROM (two-game formulation). -/
noncomputable def passiveSecrecyAdvantage
    (g : G)
    (adv : PassiveAdversary G SK) : ℝ :=
  ProbComp.boolDistAdvantage
    (execGame (passiveReal (F := F) g adv))
    (execGame (passiveRand (F := F) g adv))

/-! ## DDH reduction

The reduction receives the DDH challenge `(g, EKₐ, SPKᵦ, T)`,
embeds T as DH3, queries the ROM on the resulting DH tuple to
get a session key, and passes it directly to the adversary.

No internal coin flip — the DDH experiment's own bit handles
the real/random branching. The reduction simply forwards the
adversary's guess. -/

/-- DDH reduction: embed DDH challenge as DH3, pass ROM output
to the adversary, return the adversary's guess directly. -/
noncomputable def ddhReduction
    (adv : PassiveAdversary G SK) :
    DiffieHellman.DDHAdversary F G :=
  fun g EKₐ SPKᵦ T =>
    let inner : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
      let ikₐ ← $ᵗ F; let ikᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
      let IKₐ := ikₐ • g; let IKᵦ := ikᵦ • g; let OPKᵦ := opkᵦ • g
      let dh := (ikₐ • SPKᵦ, ikᵦ • EKₐ, T, opkᵦ • EKₐ)
      let sk ← query (spec := unifSpec + KDFOracle (G × G × G × G) SK)
                  (Sum.inr dh)
      -- No coin flip: pass sk directly, return adversary's guess
      adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk
    execGame inner

/-! ## Distributional equivalences

The core of the reduction: the executed passive games have the
same distributions as the DDH games composed with the reduction.

Both sides sample 5 scalars, compute the same DH tuple (by
`smul_smul` + `mul_comm`), query the same ROM / sample the same
random key, and call the adversary with the same values.
The only difference is the order of sampling, which doesn't
affect the joint distribution of independent uniform draws. -/
set_option linter.flexible false in
omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G]
  [Fintype SK] [DecidableEq SK] in
/-- The real passive game has the same distribution as the DDH real
game composed with the reduction. -/
private lemma passiveReal_eq_ddhExpReal
    (g : G) (adv : PassiveAdversary G SK) :
    evalDist (execGame (passiveReal (F := F) g adv)) =
    evalDist (DiffieHellman.ddhExpReal (F := F) g (ddhReduction adv)) := by
  unfold passiveReal passiveGame DiffieHellman.ddhExpReal ddhReduction execGame
  simp only [simulateQ_bind, simulateQ_query, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_add_liftComp_right,
    bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp]
  ext z; change Pr[= z | _] = Pr[= z | _]; simp_all; perm_draws

set_option linter.flexible false in
omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G]
  [Fintype SK] [DecidableEq SK] in
/-- The random passive game equals the DDH random game with the reduction. -/
private lemma passiveRand_eq_ddhExpRand
    (g : G) (adv : PassiveAdversary G SK) :
    evalDist (execGame (passiveRand (F := F) g adv)) =
    evalDist (DiffieHellman.ddhExpRand (F := F) g (ddhReduction adv)) := by
  unfold passiveRand passiveGame DiffieHellman.ddhExpRand ddhReduction execGame
  simp only [simulateQ_bind, simulateQ_query, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.simulateQ_add_liftComp_left, QueryImpl.simulateQ_add_liftComp_right,
    bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp]
  ext z; change Pr[= z | _] = Pr[= z | _]; simp_all; perm_draws

/-! ## Security theorem
X3DH passive message secrecy is at least as hard as DDH under
the Random Oracle Model for the KDF.

The bound is tight (no factor of 2) because:
- DDH real branch: T = (ekₐ*spkᵦ)•g → reduction simulates `passiveReal`
- DDH random branch: T = c•g → ROM of random input = random → simulates `passiveRand`

So `passiveSecrecyAdvantage = ddhDistAdvantage(reduction)`. -/

set_option linter.flexible false in
omit [Fintype F] [DecidableEq F] [SampleableType G] [DecidableEq G]
  [Fintype SK] [DecidableEq SK] in
/-- X3DH passive secrecy reduces to DDH under the ROM. -/
theorem passive_secrecy_le_ddh
    (g : G)
    (adv : PassiveAdversary G SK) :
    passiveSecrecyAdvantage (F := F) g adv ≤
    ProbComp.boolDistAdvantage
      (DiffieHellman.ddhExpReal (F := F) g (ddhReduction adv))
      (DiffieHellman.ddhExpRand (F := F) g (ddhReduction adv)) := by
  -- Step 1: unfold the LHS to expose the two games
  unfold passiveSecrecyAdvantage
  -- Goal is now:
  -- boolDistAdvantage (execGame (passiveReal g adv))
  --                   (execGame (passiveRand g adv))
  -- ≤ boolDistAdvantage (ddhExpReal g (ddhReduction adv))
  --                     (ddhExpRand g (ddhReduction adv))
  --
  -- We need to show these two pairs of games have the same distributions.
  -- Suffices to show:
  --   execGame (passiveReal g adv) = ddhExpReal g (ddhReduction adv)
  --   execGame (passiveRand g adv) = ddhExpRand g (ddhReduction adv)
  -- (as probability distributions)
  -- It suffices to show equality of the two distribution pairs
  suffices h : ProbComp.boolDistAdvantage
      (execGame (passiveReal (F := F) g adv))
      (execGame (passiveRand (F := F) g adv)) =
    ProbComp.boolDistAdvantage
      (DiffieHellman.ddhExpReal (F := F) g (ddhReduction adv))
      (DiffieHellman.ddhExpRand (F := F) g (ddhReduction adv)) by
    linarith
  -- Both boolDistAdvantage expressions depend only on evalDist.
  -- The distributional equivalences give us equal evalDist, hence
  -- equal probOutput, hence equal boolDistAdvantage.
  unfold ProbComp.boolDistAdvantage
  have hReal := passiveReal_eq_ddhExpReal (F := F) g adv
  have hRand := passiveRand_eq_ddhExpRand (F := F) g adv
  simp only [probOutput, hReal, hRand]
