import VersoManual
import VersoBlueprint
import PQXDHLean.X3DH.X3DHPassiveMessageSecrecy
import PQXDHDocs.SourceBlock

open Verso.Genre Manual
open Informal


#doc (Manual) "Passive Message Secrecy" =>
%%%
tag := "passive_secrecy"
%%%

:::group "passive_secrecy_core"
Passive message secrecy game, DDH reduction, and tight security bound
under the Random Oracle Model.
:::

Passive message secrecy for X3DH under the Random Oracle Model,
using VCV-io for security game definitions.

# Random Oracle Model

In the real protocol, the KDF (HKDF-SHA-256, §2.5, p. 473) is a
deterministic function. In the security proof, we replace it with a *random
oracle*: a function that, on each new input, returns a uniformly
random output and caches it for consistency (same input always
gives the same output).

This is the standard ROM assumption from the paper (assumption 4).
It lets us argue that the session key is indistinguishable from
random whenever the KDF input contains a fresh random component
(as happens when DH3 is replaced with a random group element in
the DDH reduction).

:::definition "exec_game" (lean := "execGame") (parent := "passive_secrecy_core")
To compute probabilities, the KDF oracle is implemented as
fresh uniform samples (equivalent to ROM for single-query games).
This bridges VCV-io's oracle computations to concrete probability
distributions.
:::

# Passive adversary

:::definition "passive_adversary" (lean := "PassiveAdversary") (parent := "passive_secrecy_core")
A passive adversary sees the public transcript (five group elements)
and a candidate session key. It has ROM access and outputs a Bool guess.
:::

# Two-game formulation

Both games share a common structure that samples keys, computes
public values and the DH tuple, then obtains a session key via
a callback. The real and random games differ only in how the
session key is obtained.

:::definition "passive_real" (lean := "passiveReal") (parent := "passive_secrecy_core")
In the real game, the session key is obtained by querying the
random oracle on the actual DH tuple.
:::

:::definition "passive_rand" (lean := "passiveRand") (parent := "passive_secrecy_core")
In the random game, the session key is sampled uniformly at random,
independent of the DH tuple.
:::

# Advantage

:::definition "passive_secrecy_advantage" (lean := "passiveSecrecyAdvantage") (parent := "passive_secrecy_core")
The passive secrecy advantage measures an adversary's ability to
distinguish the real game from the random game. A value of 0 means
the adversary cannot distinguish them.
:::

# DDH reduction

:::definition "ddh_reduction" (lean := "ddhReduction") (parent := "passive_secrecy_core")
Given a passive adversary A, we construct a DDH adversary B that
embeds the DDH challenge (g, EK_a, SPK_b, T) as DH3. No internal
coin flip: the DDH experiment's own bit handles real/random branching.
This makes the bound tight (no factor of 2).
:::

# Distributional equivalences

The core of the reduction: the executed passive games have the
same distributions as the DDH games composed with the reduction.

The first equivalence shows that the real passive game equals the
DDH real game composed with the reduction (by sampling order
independence and `smul_smul` + `mul_comm`).

The second equivalence shows that the random passive game equals
the DDH random game. The RHS has an extra unused draw from DDH;
the proof adds a matching unused draw to the LHS via
`probOutput_bind_const`, then permutes independent draws via the
`perm_draws` tactic.

Both proofs are fully mechanized (no `sorry`) using the custom
`perm_draws` tactic, which automatically computes the draw
permutation via de Bruijn index analysis and emits the minimal
swap sequence.

# Security theorem

:::theorem "passive_secrecy_le_ddh" (lean := "passive_secrecy_le_ddh") (parent := "passive_secrecy_core") (tags := "x3dh, security, ddh, rom") (effort := "medium") (priority := "high")
The passive secrecy advantage of any adversary is bounded by
the DDH advantage of {uses "ddh_reduction"}[]. This is a tight
reduction: no factor-of-2 loss.
:::

:::proof "passive_secrecy_le_ddh"
Unfold {uses "passive_secrecy_advantage"}[], show the two
`boolDistAdvantage` expressions are equal via the distributional
equivalence lemmas, and conclude by `linarith`.
:::

```source passive_secrecy_le_ddh
```
