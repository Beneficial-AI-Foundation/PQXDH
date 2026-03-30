/-
Computational security properties of Diffie-Hellman.

## Relationship to VCV-io

The algebraic signature in `DH.lean` — `[Field F] [AddCommGroup G]
[Module F G]` with `DH (a : F) (B : G) := a • B` — was chosen to
match VCV-io's `DiffieHellman.lean`, which defines the standard
hardness assumptions (DLog, CDH, DDH) over exactly this structure:

  ```
  variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
  ```

The additional VCV-io instances (`Fintype`, `SampleableType`,
`DecidableEq`) are only needed for probabilistic sampling and
experiment evaluation — they are not required for the algebraic
proofs in this project. When they are added, the DLog/CDH/DDH
games from VCV-io apply directly:

  - `DiffieHellman.dlogExp g adversary` — given `(g, x • g)`, find `x`
  - `DiffieHellman.cdhExp g adversary` — given `(g, a•g, b•g)`, find `(a*b)•g`
  - `DiffieHellman.ddhExp g adversary` — distinguish `(a*b)•g` from random

VCV-io also provides:
  - `ddhGuessAdvantage` / `ddhDistAdvantage` with a proven factor-of-2
    equivalence theorem (`ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage`)
  - `dlogGenerable` — the DLog relation is generable when `(· • g)` is
    bijective, enabling Fiat-Shamir style reductions
  - `KEMScheme` with a full `IND_CCA_Game` — a concrete replacement for
    the opaque `KEM_IND_CCA` in `SecurityDefs.lean`
  - A complete ElGamal IND-CPA proof reducing to DDH

## What VCV-io does not yet provide

The PQXDH paper's Theorem 2 requires **gapDH** (CDH with a DDH
decision oracle), which VCV-io does not define. It is architecturally
straightforward to build: define a DDH oracle spec, then write the
gapDH experiment using `simulateQ` to provide the oracle. The
`OracleComp` framework's `+` combinator for oracle specs makes this
natural.

## Current status

The security properties in `SecurityDefs.lean` (e.g. `GapDH_Hard`)
remain opaque `Prop`s. Connecting them to VCV-io's concrete game
definitions is a future step that would replace these axioms with
advantage bounds over `ProbComp Bool` experiments.
-/
import PQXDHLean.DH.DH
