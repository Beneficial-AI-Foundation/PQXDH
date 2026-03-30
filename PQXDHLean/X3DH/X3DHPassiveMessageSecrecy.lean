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
import PQXDHLean.X3DH.X3DH
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.RandomOracle

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

/-- Real game: adversary receives the actual X3DH session key. -/
def passiveReal
    (g : G)
    (adv : PassiveAdversary G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
  let ikₐ ← $ᵗ F; let ekₐ ← $ᵗ F
  let ikᵦ ← $ᵗ F; let spkᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
  let IKₐ := ikₐ • g; let EKₐ := ekₐ • g
  let IKᵦ := ikᵦ • g; let SPKᵦ := spkᵦ • g; let OPKᵦ := opkᵦ • g
  let dh := X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ (some OPKᵦ)
  let sk ← query (spec := unifSpec + KDFOracle (G × G × G × G) SK) (Sum.inr dh)
  adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk

/-- Random game: adversary receives a uniformly random key. -/
def passiveRand
    (g : G)
    (adv : PassiveAdversary G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
  let ikₐ ← $ᵗ F; let ekₐ ← $ᵗ F
  let ikᵦ ← $ᵗ F; let spkᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
  let IKₐ := ikₐ • g; let EKₐ := ekₐ • g
  let IKᵦ := ikᵦ • g; let SPKᵦ := spkᵦ • g; let OPKᵦ := opkᵦ • g
  let sk ← $ᵗ SK
  adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk

/-! ## Executing the games

To compute probabilities, the KDF oracle must be implemented.
We use `randomOracle` (lazy cached uniform sampling) and run
the result via `StateT.run'` with an empty initial cache. -/

/-- Execute an oracle computation with ROM for the KDF. -/
noncomputable def execWithROM
    (comp : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool) :
    ProbComp Bool :=
  let ro : QueryImpl (KDFOracle (G × G × G × G) SK)
    (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp) := randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp)
  StateT.run' (simulateQ (idImpl + ro) comp) ∅

/-! ## Advantage

The advantage is `|Pr[true | real] - Pr[true | rand]|`,
using VCV-io's `boolDistAdvantage`. -/

/-- Passive secrecy advantage under the ROM (two-game formulation). -/
noncomputable def passiveSecrecyAdvantage
    (g : G)
    (adv : PassiveAdversary G SK) : ℝ :=
  ProbComp.boolDistAdvantage
    (execWithROM (passiveReal (F := F) g adv))
    (execWithROM (passiveRand (F := F) g adv))

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
    execWithROM inner

/-! ## Security theorem

X3DH passive message secrecy is at least as hard as DDH under
the Random Oracle Model for the KDF.

The bound is tight (no factor of 2) because:
- DDH real branch: T = (ekₐ*spkᵦ)•g → reduction simulates `passiveReal`
- DDH random branch: T = c•g → ROM of random input = random → simulates `passiveRand`

So `passiveSecrecyAdvantage = ddhDistAdvantage(reduction)`. -/

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
  -- boolDistAdvantage (execWithROM (passiveReal g adv))
  --                   (execWithROM (passiveRand g adv))
  -- ≤ boolDistAdvantage (ddhExpReal g (ddhReduction adv))
  --                     (ddhExpRand g (ddhReduction adv))
  --
  -- We need to show these two pairs of games have the same distributions.
  -- Suffices to show:
  --   execWithROM (passiveReal g adv) = ddhExpReal g (ddhReduction adv)
  --   execWithROM (passiveRand g adv) = ddhExpRand g (ddhReduction adv)
  -- (as probability distributions)
  -- It suffices to show equality of the two distribution pairs
  suffices h : ProbComp.boolDistAdvantage
      (execWithROM (passiveReal (F := F) g adv))
      (execWithROM (passiveRand (F := F) g adv)) =
    ProbComp.boolDistAdvantage
      (DiffieHellman.ddhExpReal (F := F) g (ddhReduction adv))
      (DiffieHellman.ddhExpRand (F := F) g (ddhReduction adv)) by
    linarith
  sorry
