/-
Passive message secrecy for X3DH.

## Goal

Formalize the simplest meaningful security property of X3DH:
a passive eavesdropper who observes only public values cannot
distinguish the session key from a random key.

## The game

  1. Sample all private keys uniformly from F.
  2. Compute public keys and the real session key via X3DH.
  3. Sample a random key.
  4. Flip a bit b; give the adversary the public transcript
     and either the real key (b = true) or the random key.
  5. The adversary outputs a guess b'.
  6. Returns (b == b').

Security means: for all efficient adversaries, the probability
of returning true is negligibly close to 1/2.

## Connection to VCV-io

The passive adversary and security game are expressed using
VCV-io's `ProbComp` (= `OracleComp unifSpec`), making them
compatible with VCV-io's probability reasoning (`Pr[...]`),
DDH game (`DiffieHellman.ddhExp`), and advantage bounds.

The security reduction (passive secrecy → DDH) embeds the
DDH challenge into one of the X3DH DH values and forwards
the adversary's guess.

Reference: Bhargavan et al., USENIX Security 2024.
  The passive case is implicit in Theorem 2 (§5.2), which proves
  the stronger active-adversary (AKE game) version.
-/
import PQXDHLean.X3DH.X3DH
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

open OracleComp OracleSpec

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {SK : Type} [Fintype SK] [DecidableEq SK] [SampleableType SK]

/-! ## Passive adversary

A passive adversary sees the public transcript of an X3DH session
(all five public keys) and a candidate session key. It outputs a
`ProbComp Bool` guess: true = "real key", false = "random key".

The adversary may use internal randomness (it returns `ProbComp Bool`,
not plain `Bool`), but has no oracle access beyond uniform sampling. -/

/-- A passive X3DH adversary. Given the public transcript
(IKₐ, EKₐ, IKᵦ, SPKᵦ, OPKᵦ) and a candidate session key,
outputs a probabilistic guess. -/
def PassiveAdversary (G SK : Type) :=
  G → G → G → G → G → SK → ProbComp Bool

/-! ## Passive secrecy game

The challenger runs a full X3DH session honestly, then presents
the adversary with either the real session key or a random one.
The adversary must guess which.

The KDF is modeled abstractly: `kdf : (G × G × G × G) → SK`
maps the four DH values to a session key. In the full security
proof, this would be a random oracle; here we leave it as a
parameter. -/

/-- Passive X3DH secrecy game. Returns true iff the adversary
correctly guesses whether it received the real or random key. -/
def passiveSecrecyGame
    (g : G) (kdf : (G × G × G × G) → SK)
    (adv : PassiveAdversary G SK) : ProbComp Bool := do
  -- Sample all private keys
  let ikₐ ← $ᵗ F; let ekₐ ← $ᵗ F
  let ikᵦ ← $ᵗ F; let spkᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
  -- Compute public keys
  let IKₐ := ikₐ • g; let EKₐ := ekₐ • g
  let IKᵦ := ikᵦ • g; let SPKᵦ := spkᵦ • g; let OPKᵦ := opkᵦ • g
  -- Compute real session key via X3DH
  let dh := X3DH_Alice ikₐ ekₐ IKᵦ SPKᵦ (some OPKᵦ)
  let sk_real := kdf dh
  -- Sample random session key
  let sk_rand ← $ᵗ SK
  -- Challenge: flip bit, present real or random
  let b ← $ᵗ Bool
  let sk_challenge := if b then sk_real else sk_rand
  -- Adversary guesses
  let b' ← adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk_challenge
  return (b == b')

/-! ## Advantage

The adversary's advantage is the absolute distance from random
guessing (1/2). This mirrors VCV-io's `ddhGuessAdvantage`. -/

/-- Passive secrecy advantage: |Pr[game returns true] - 1/2|. -/
noncomputable def passiveSecrecyAdvantage
    (g : G) (kdf : (G × G × G × G) → SK)
    (adv : PassiveAdversary G SK) : ℝ :=
  |(Pr[= true | passiveSecrecyGame (F := F) g kdf adv]).toReal - 1 / 2|

/-! ## DDH reduction (statement only)

The security theorem states: the passive secrecy advantage is
bounded by the DDH advantage. The proof constructs a DDH
adversary B from a passive X3DH adversary A:

  B receives DDH challenge (g, A = a•g, B = b•g, T).
  B embeds (A, B, T) as (EKₐ, SPKᵦ, DH3) in a simulated
  X3DH session, samples the remaining keys honestly, computes
  the session key using T as DH3, and forwards A's guess.

  If T = (a*b)•g (real DH), the session key is correct.
  If T is random, the session key is independent of the
  real one, so A's advantage vanishes.

  Therefore: passiveSecrecyAdvantage ≤ ddhGuessAdvantage + ε_kdf
  where ε_kdf accounts for the KDF distinguishing gap.
-/

/-- DDH reduction: given a passive X3DH adversary, construct a
DDH adversary that embeds the challenge into the X3DH session. -/
def ddhReduction
    (kdf : (G × G × G × G) → SK)
    (adv : PassiveAdversary G SK) :
    DiffieHellman.DDHAdversary F G :=
  fun g EKₐ SPKᵦ T => do
    -- T is the DDH challenge: either (ekₐ * spkᵦ) • g or random
    -- Sample remaining private keys honestly
    let ikₐ ← $ᵗ F; let ikᵦ ← $ᵗ F; let opkᵦ ← $ᵗ F
    -- Compute remaining public keys
    let IKₐ := ikₐ • g; let IKᵦ := ikᵦ • g; let OPKᵦ := opkᵦ • g
    -- Build DH tuple using T as DH3
    let dh1 := ikₐ • SPKᵦ        -- DH(ikₐ, SPKᵦ)
    let dh2 := ikᵦ • EKₐ         -- DH(ikᵦ, EKₐ) — note: Bob's view, but
                                   -- we don't know ekₐ, so we use ikᵦ • EKₐ
                                   -- which equals DH(ekₐ, IKᵦ) by commutativity
                                   -- when EKₐ = ekₐ • g and IKᵦ = ikᵦ • g
    let dh3 := T                   -- The DDH challenge replaces DH(ekₐ, SPKᵦ)
    let dh4 := opkᵦ • EKₐ         -- DH(opkᵦ, EKₐ) = DH(ekₐ, OPKᵦ) by comm.
    let sk := kdf (dh1, dh2, dh3, dh4)
    -- Challenge the passive adversary
    let sk_rand ← $ᵗ SK
    let b ← $ᵗ Bool
    let sk_challenge := if b then sk else sk_rand
    let b' ← adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk_challenge
    return (b == b')
