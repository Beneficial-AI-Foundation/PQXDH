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

In VCV-io, the ROM is modeled as an oracle spec with a cached
implementation:

```
-- Oracle spec: maps DH tuples to session keys
abbrev KDFOracle (I K : Type) := I ->o K

-- Implementation: lazy cached uniform sampling
randomOracle : QueryImpl (KDFOracle I K)
  (StateT (KDFOracle I K).QueryCache ProbComp)
```

The game has access to this oracle via
`OracleComp (unifSpec + KDFOracle ...)`. To compute probabilities,
we execute the game with the ROM using `simulateQ`:

```
noncomputable def execWithROM
    (comp : OracleComp (unifSpec + KDFOracle (G * G * G * G) SK) Bool)
    : ProbComp Bool :=
  let ro := randomOracle
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (...)
  StateT.run' (simulateQ (idImpl + ro) comp) empty
```

# Passive adversary

A passive adversary sees the public transcript and a candidate
session key. It has ROM access and outputs a Bool guess:

```
abbrev PassiveAdversary (G SK : Type) :=
  G -> G -> G -> G -> G -> SK ->
    OracleComp (KDFOracle (G * G * G * G) SK) Bool
```

# Two-game formulation

Both games share a common structure that samples keys, computes
public values and the DH tuple, then obtains a session key via
a callback:

```
private def passiveGame (g : G)
    (adv : PassiveAdversary G SK)
    (getSK : (G * G * G * G) ->
             OracleComp (unifSpec + KDFOracle (G * G * G * G) SK) SK)
    : OracleComp (unifSpec + KDFOracle (G * G * G * G) SK) Bool := do
  let ikA <- $t F; let ekA <- $t F
  let ikB <- $t F; let spkB <- $t F; let opkB <- $t F
  let IKA := ikA . g; let EKA := ekA . g
  let IKB := ikB . g; let SPKB := spkB . g; let OPKB := opkB . g
  let dh := X3DH_Alice ikA ekA IKB SPKB (some OPKB)
  let sk <- getSK dh
  adv IKA EKA IKB SPKB OPKB sk
```

The real and random games differ only in getSK:

```
-- Real: query ROM on DH tuple
def passiveReal (g : G) (adv : PassiveAdversary G SK) :=
  passiveGame g adv fun dh => query (Sum.inr dh)

-- Random: sample uniformly, ignore DH tuple
def passiveRand (g : G) (adv : PassiveAdversary G SK) :=
  passiveGame g adv fun _ => $t SK
```

# Advantage

```
noncomputable def passiveSecrecyAdvantage (g : G)
    (adv : PassiveAdversary G SK) : R :=
  ProbComp.boolDistAdvantage
    (execWithROM (passiveReal g adv))
    (execWithROM (passiveRand g adv))
```

The advantage is |Pr\[true | real\] - Pr\[true | rand\]|.
A value of 0 means the adversary cannot distinguish the games.

# DDH reduction

Given a passive adversary A, we construct a DDH adversary B that
embeds the DDH challenge (g, EKA, SPKB, T) as DH3:

```
noncomputable def ddhReduction
    (adv : PassiveAdversary G SK) :
    DiffieHellman.DDHAdversary F G :=
  fun g EKA SPKB T =>
    let inner := do
      let ikA <- $t F; let ikB <- $t F; let opkB <- $t F
      let IKA := ikA . g; let IKB := ikB . g; let OPKB := opkB . g
      let dh := (ikA . SPKB, ikB . EKA, T, opkB . EKA)
      let sk <- query (Sum.inr dh)
      adv IKA EKA IKB SPKB OPKB sk
    execWithROM inner
```

No internal coin flip: the DDH experiment's own bit handles
real/random branching. This makes the bound tight (no factor of 2).

# Security theorem

```
theorem passive_secrecy_le_ddh (g : G)
    (adv : PassiveAdversary G SK) :
    passiveSecrecyAdvantage g adv <=
    ProbComp.boolDistAdvantage
      (DiffieHellman.ddhExpReal g (ddhReduction adv))
      (DiffieHellman.ddhExpRand g (ddhReduction adv))
```

The proof reduces to two distributional equivalence lemmas
(currently sorry):

- The real passive game has the same distribution as the DDH real
  game composed with the reduction (by sampling order independence
  and smul_smul + mul_comm).
- The random passive game has the same distribution as the DDH
  random game (by ROM freshness: querying on an input containing
  a random component produces uniform output).

The main theorem itself is fully proved from these two lemmas.
