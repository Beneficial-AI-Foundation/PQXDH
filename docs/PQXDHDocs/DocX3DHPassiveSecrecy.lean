import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Passive Message Secrecy" =>

Passive message secrecy for X3DH under the Random Oracle Model,
using VCV-io for security game definitions.

# Random Oracle Model

In the real protocol, the KDF (HKDF-SHA-256) is a deterministic
function. In the security proof, we replace it with a *random
oracle*: a function that, on each new input, returns a uniformly
random output and caches it for consistency (same input always
gives the same output).

This is the standard ROM assumption from the paper (assumption 4).
It lets us argue that the session key is indistinguishable from
random whenever the KDF input contains a fresh random component
(as happens when DH3 is replaced with a random group element in
the DDH reduction).

To compute probabilities, the KDF oracle is implemented as
fresh uniform samples (equivalent to ROM for single-query games):

```
noncomputable def execGame
    (comp : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool) :
    ProbComp Bool :=
  let kdfImpl : QueryImpl (KDFOracle (G × G × G × G) SK) ProbComp :=
    fun _ => $ᵗ SK
  let idImpl : QueryImpl unifSpec ProbComp := QueryImpl.ofLift unifSpec ProbComp
  simulateQ (idImpl + kdfImpl) comp
```

# Passive adversary

A passive adversary sees the public transcript and a candidate
session key. It has ROM access and outputs a Bool guess:

```
abbrev PassiveAdversary (G SK : Type) :=
  G → G → G → G → G → SK → OracleComp (KDFOracle (G × G × G × G) SK) Bool
```

# Two-game formulation

Both games share a common structure that samples keys, computes
public values and the DH tuple, then obtains a session key via
a callback:

```
private def passiveGame (g : G)
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
```

The real and random games differ only in `getSK`:

```
-- Real: query ROM on DH tuple
def passiveReal (g : G) (adv : PassiveAdversary G SK) :=
  passiveGame g adv fun dh =>
    query (spec := unifSpec + KDFOracle (G × G × G × G) SK) (Sum.inr dh)

-- Random: sample uniformly, ignore DH tuple
def passiveRand (g : G) (adv : PassiveAdversary G SK) :=
  passiveGame g adv fun _ => $ᵗ SK
```

# Advantage

```
noncomputable def passiveSecrecyAdvantage (g : G)
    (adv : PassiveAdversary G SK) : ℝ :=
  ProbComp.boolDistAdvantage
    (execGame (passiveReal g adv))
    (execGame (passiveRand g adv))
```

The advantage is |Pr\[true | real\] - Pr\[true | rand\]|.
A value of 0 means the adversary cannot distinguish the games.

# DDH reduction

Given a passive adversary A, we construct a DDH adversary B that
embeds the DDH challenge `(g, EKₐ, SPKᵦ, T)` as DH3:

```
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
      adv IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ sk
    execGame inner
```

No internal coin flip: the DDH experiment's own bit handles
real/random branching. This makes the bound tight (no factor of 2).

# Distributional equivalences

The core of the reduction: the executed passive games have the
same distributions as the DDH games composed with the reduction.

- `passiveReal_eq_ddhExpReal`: the real passive game equals the
  DDH real game composed with the reduction (by sampling order
  independence and `smul_smul` + `mul_comm`).

- `passiveRand_eq_ddhExpRand`: the random passive game equals
  the DDH random game. The RHS has an extra unused draw `c`
  from DDH; the proof adds a matching unused draw to the LHS
  via `probOutput_bind_const`, then permutes independent draws
  via the `perm_draws` tactic.

Both proofs are fully mechanized (no `sorry`) using the custom
`perm_draws` tactic, which automatically computes the draw
permutation via de Bruijn index analysis and emits the
minimal swap sequence.

# Security theorem

```
theorem passive_secrecy_le_ddh (g : G)
    (adv : PassiveAdversary G SK) :
    passiveSecrecyAdvantage g adv ≤
    ProbComp.boolDistAdvantage
      (DiffieHellman.ddhExpReal g (ddhReduction adv))
      (DiffieHellman.ddhExpRand g (ddhReduction adv))
```

The proof unfolds `passiveSecrecyAdvantage`, shows the two
`boolDistAdvantage` expressions are equal (via the distributional
equivalence lemmas), and concludes by `linarith`.
