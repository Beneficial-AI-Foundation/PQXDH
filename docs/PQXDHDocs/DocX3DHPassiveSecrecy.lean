import Verso
import VersoManual
open Verso.Genre Manual
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Passive Message Secrecy" =>

Passive message secrecy for X3DH under the Random Oracle Model,
using VCV-io for security game definitions.

# Goal

A passive eavesdropper who observes only public values cannot
distinguish the session key from a random key.

# Random Oracle Model

The KDF is modeled as a random oracle (KDFOracle, defined in
KDF.lean). The game has oracle access to this KDF: on first query
for an input, the oracle samples a uniform random output and
caches it. Same input always returns the same output.

# Two-game formulation

Instead of a single game with a hidden coin flip, we define two
games and measure the adversary's ability to distinguish them:

- Real game (passiveReal): adversary receives the actual session
  key, obtained by querying the ROM on the X3DH DH tuple.
- Random game (passiveRand): adversary receives a uniformly random
  key, independent of the DH tuple.

Both games share a common structure (passiveGame): sample 5 private
keys, compute public keys and the DH tuple, obtain a session key
via a callback (getSK), and pass it to the adversary. The real and
random games differ only in getSK.

# Advantage

The passive secrecy advantage is defined as
|Pr\[true | real\] - Pr\[true | rand\]| using VCV-io's
boolDistAdvantage. An advantage of 0 means the adversary cannot
tell the games apart; an advantage of 1 means it always can.

# DDH reduction

Given a passive adversary A, we construct a DDH adversary B
(ddhReduction) that:

1. Receives the DDH challenge (g, EKA, SPKB, T)
2. Samples the remaining keys honestly (ikA, ikB, opkB)
3. Embeds T as DH3 in the X3DH DH tuple
4. Queries the ROM on the DH tuple to get a session key
5. Passes the session key directly to A (no coin flip)
6. Returns A's guess as its own

The reduction has no internal coin flip. The DDH experiment's own
bit handles the real/random branching. This makes the bound tight
(no factor of 2).

# Security theorem

The passive secrecy advantage of any adversary A is bounded by the
DDH distinguishing advantage of the reduction B:

  passiveSecrecyAdvantage(A) <= ddhDistAdvantage(B)

The proof reduces to two distributional equivalence lemmas:

- The real passive game has the same distribution as the DDH real
  game composed with the reduction.
- The random passive game has the same distribution as the DDH
  random game composed with the reduction.

The main theorem is fully proved from these two lemmas. The lemmas
themselves require showing that two sampling sequences produce the
same joint distribution (sampling order independence plus Module
commutativity). This is the current formalization frontier, matching
the semantic step that CryptoVerif handles as a built-in swap axiom.
