/-
Passive message secrecy for X3DH under the Random Oracle Model.

This file provides the ROM-based definitions for the passive secrecy
game, replacing the `uniformSampleImpl`-based `execGame` from
`X3DHPassiveMessageSecrecyUniform.lean` with one that uses VCVio's
`randomOracle` (lazy cached uniform sampling).

## Why ROM matters

The PQXDH specification (Section 4) states that the security
analysis models "the hash function as a random oracle." In the
ROM, the random oracle is a public function: all parties,
including the adversary, can query it. A proper `randomOracle`
preserves consistency (same input → same output), so if the
adversary queries ROM on the DH tuple, it recovers the real
session key. This is what makes the passive secrecy game
non-trivial and the DDH reduction meaningful.

With `uniformSampleImpl` (as in the Uniform variant), every query
returns a fresh independent sample, collapsing the real/random
distinction and making the security theorem vacuous.

## Implementation

`execGame` follows the pattern from VCVio's `Examples/BR93.lean`:
- `randomOracle` implements the KDF as a `StateT QueryCache ProbComp`
- `QueryImpl.ofLift` lifts `unifSpec` into the same monad
- `.run' ∅` executes from the empty cache, discarding final state

The return type is still `ProbComp Bool`, so downstream definitions
(`passiveSecrecyAdvantage`, DDH reduction) have the same types.

## Proof status

Security proofs require game-hopping with identical-until-bad
arguments. VCVio's ROM game-hopping infrastructure is still under
development (cf. `sorry` proofs in `Examples/BR93.lean`).

Reference: Bhargavan et al., USENIX Security 2024.
-/
import PQXDHLean.X3DH.X3DH
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.SimSemantics.Append
import VCVio.CryptoFoundations.SecExp

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
abbrev PassiveAdversaryROM (G SK : Type) :=
  G → G → G → G → G → SK → OracleComp (KDFOracle (G × G × G × G) SK) Bool

/-! ## Passive secrecy games (two-game formulation)

The real and random games differ only in how the session key is
obtained. Both give the adversary the public transcript and oracle
access to the KDF (ROM). -/

/-- Common game structure: sample keys, compute public values and
DH tuple, obtain a session key via `getSK`, and pass it to the
adversary. -/
private def passiveGameROM
    (g : G)
    (adv : PassiveAdversaryROM G SK)
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
def passiveRealROM
    (g : G)
    (adv : PassiveAdversaryROM G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool :=
  passiveGameROM (F := F) g adv fun dh =>
    query (spec := unifSpec + KDFOracle (G × G × G × G) SK) (Sum.inr dh)

/-- Random game: session key sampled uniformly at random. -/
def passiveRandROM
    (g : G)
    (adv : PassiveAdversaryROM G SK) :
    OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool :=
  passiveGameROM (F := F) g adv fun _ => $ᵗ SK

/-! ## Executing the games under the ROM

The KDF oracle is implemented via VCVio's `randomOracle`: a lazy
cached uniform sampler that returns the same output for the same
input. This preserves ROM consistency — if the adversary queries
ROM on the DH tuple, it gets the actual session key.

The implementation follows the pattern from `Examples/BR93.lean`:
- `randomOracle` : `QueryImpl (KDFOracle ...) (StateT QueryCache ProbComp)`
- `QueryImpl.ofLift` lifts `unifSpec` into the stateful monad
- `.run' ∅` executes with empty initial cache, discarding final state

The return type is `ProbComp Bool`, matching the uniform variant. -/

/-- Execute an oracle computation implementing the KDF as a
proper random oracle (lazy cached uniform sampling). -/
noncomputable def execGameROM
    (comp : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool) :
    ProbComp Bool :=
  let ro : QueryImpl (KDFOracle (G × G × G × G) SK)
           (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp) :=
    randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (KDFOracle (G × G × G × G) SK).QueryCache ProbComp)
  (simulateQ (idImpl + ro) comp).run' ∅

/-! ## Advantage

The passive secrecy advantage under the ROM. Unlike the uniform
variant, this is NOT trivially 0: the real game gives the adversary
`sk = ROM(dh)`, and an adversary that queries `ROM(dh)` can
distinguish it from a random key. -/

/-- Passive secrecy advantage under the ROM (two-game formulation). -/
noncomputable def passiveSecrecyAdvantageROM
    (g : G)
    (adv : PassiveAdversaryROM G SK) : ℝ :=
  ProbComp.boolDistAdvantage
    (execGameROM (passiveRealROM (F := F) g adv))
    (execGameROM (passiveRandROM (F := F) g adv))
