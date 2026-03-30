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

/-! ## Passive secrecy game

The challenger runs a full X3DH session, queries the KDF oracle
to derive the session key, then challenges the adversary with
either the real key or a random one. -/

/-- Passive X3DH secrecy game under the ROM. The KDF is an oracle
`(G × G × G × G) →ₒ SK` implemented by `randomOracle`. -/
def passiveSecrecyGame
    (g : G)
    (adv : PassiveAdversary G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
  -- Sample all private keys
  let ikₐ ← $ᵗ F; let ekₐ ← $ᵗ F
  let ikᵦ ← $ᵗ F; let spkᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
  -- Compute public keys
  let IKₐ := ikₐ • g; let EKₐ := ekₐ • g
  let IKᵦ := ikᵦ • g; let SPKᵦ := spkᵦ • g; let OPKᵦ := opkᵦ • g
  -- Compute DH tuple via X3DH
  let dh := X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ (some OPKᵦ)
  -- Query KDF oracle (random oracle) to get session key
  let sk_real ← query (spec := unifSpec + KDFOracle (G × G × G × G) SK) (Sum.inr dh)
  -- Sample random session key
  let sk_rand ← $ᵗ SK
  -- Challenge: flip bit, present real or random
  let b ← $ᵗ Bool
  let sk_challenge := if b then sk_real else sk_rand
  -- Adversary guesses (with ROM access)
  let b' ← adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk_challenge
  return (b == b')

/-! ## Executing the game

To compute probabilities, the KDF oracle must be implemented.
We use `randomOracle` (lazy cached uniform sampling) and run
the result via `StateT.run'` with an empty initial cache. -/

/-- Execute the passive secrecy game: implement the KDF oracle
as a random oracle and discard the cache state. -/
noncomputable def execPassiveSecrecyGame
    (g : G)
    (adv : PassiveAdversary G SK) : ProbComp Bool :=
  let ro : QueryImpl (KDFOracle (G × G × G × G) SK)
    (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp) := randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp)
  StateT.run' (simulateQ (idImpl + ro) (passiveSecrecyGame (F := F) g adv)) ∅

/-! ## Advantage -/

/-- Passive secrecy advantage under the ROM. -/
noncomputable def passiveSecrecyAdvantage
    (g : G)
    (adv : PassiveAdversary G SK) : ℝ :=
  (execPassiveSecrecyGame (F := F) g adv).boolBiasAdvantage

/-! ## DDH reduction

The reduction builds a DDH adversary from a passive X3DH adversary.
It receives the DDH challenge `(g, EKₐ, SPKᵦ, T)`, embeds T as DH3,
queries the KDF oracle on the resulting DH tuple, and forwards the
passive adversary's guess.

The reduction has ROM access (it queries the KDF oracle), so it
returns `OracleComp (KDFOracle ...) Bool` — matching VCV-io's
`DDHAdversary` after oracle execution. -/

/-- DDH reduction: embed DDH challenge as DH3 in an X3DH session. -/
def ddhReduction
    (adv : PassiveAdversary G SK) :
    DiffieHellman.DDHAdversary F G :=
  fun g EKₐ SPKᵦ T =>
    -- The reduction runs passiveSecrecyGame-like logic internally,
    -- executing the KDF ROM via simulateQ inside ProbComp.
    let inner : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
      -- Sample remaining private keys
      let ikₐ ← $ᵗ F; let ikᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
      -- Compute remaining public keys
      let IKₐ := ikₐ • g; let IKᵦ := ikᵦ • g; let OPKᵦ := opkᵦ • g
      -- Build DH tuple: T replaces DH3
      let dh := (ikₐ • SPKᵦ, ikᵦ • EKₐ, T, opkᵦ • EKₐ)
      -- Query ROM to hash DH tuple to session key
      let sk ← query (spec := unifSpec + KDFOracle (G × G × G × G) SK)
                  (Sum.inr dh)
      -- Challenge
      let sk_rand ← $ᵗ SK
      let b ← $ᵗ Bool
      let sk_challenge := if b then sk else sk_rand
      let b' ← adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk_challenge
      return (b == b')
    -- Execute with ROM, producing ProbComp Bool
    let ro : QueryImpl (KDFOracle (G × G × G × G) SK)
      (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp) := randomOracle
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp)
    StateT.run' (simulateQ (idImpl + ro) inner) ∅

/-! ## Security theorem

X3DH passive message secrecy is at least as hard as DDH
under the Random Oracle Model for the KDF. -/

/-- X3DH passive secrecy reduces to DDH under the ROM. -/
theorem passive_secrecy_le_ddh
    (g : G)
    (adv : PassiveAdversary G SK) :
    passiveSecrecyAdvantage (F := F) g adv ≤
    (DiffieHellman.ddhExp (F := F) g (ddhReduction adv)).boolBiasAdvantage := by
  sorry
