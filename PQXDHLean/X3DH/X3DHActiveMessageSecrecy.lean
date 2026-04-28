/-
Active message secrecy for X3DH under the Random Oracle Model.

## Goal

Formalize X3DH security under a full **active adversary** model
(AKE — Authenticated Key Exchange game): a network-controlling
attacker who can start new sessions, inject or modify messages,
corrupt long-term keys, and reveal completed session keys.

This is strictly stronger than the passive-adversary setting
already formalized in `X3DHPassiveMessageSecrecy.lean`.

## The AKE game

The adversary has access to five oracle queries (see
`SecurityDefs.AKE_Query`):

  1. **NewSession(A, B, role)** — start a new protocol session
     between parties A and B in the given role (initiator or
     responder). Returns a fresh session id.
  2. **Send(sid, msg)** — deliver a (possibly adversary-modified)
     message to session `sid`. The session advances its protocol
     state. Signature verification happens here — forged prekey
     bundles are rejected (bounded by Sig EUF-CMA).
  3. **Corrupt(party)** — leak a party's long-term identity secret
     key. Records the corruption timestamp in game state.
  4. **RevealSessionKey(sid)** — leak the session key of a
     completed session. Fails if the session is not yet accepted.
  5. **Test(sid)** — (once per game) on a designated fresh session,
     the challenger flips a bit `b` and returns either the real
     session key (`b = true`) or a fresh uniform random key
     (`b = false`). The adversary eventually outputs a guess `b'`.

## Freshness

The theorem only promises security for a **fresh** test session.
A session is fresh if:
  - its session key was not revealed,
  - the matching partner's session key was not revealed, and
  - not both parties' long-term identity keys were corrupted
    before the session completed.

These conditions rule out trivial attacks (e.g., just calling
`RevealSessionKey` on the test session) and are packaged in the
`Freshness` structure from `SecurityDefs.lean`.

## Relationship to passive secrecy

A passive adversary is an active adversary that simply never uses
`Send`, `Corrupt`, or `RevealSessionKey`. So active security
implies passive security; the converse does NOT hold.

The DDH reduction used in `X3DHPassiveMessageSecrecy.lean` does
not extend directly. Active security reduces to **gapDH** (CDH
with a DDH oracle) — stronger than DDH — because:
  - Identity keys are used for both DH and XEdDSA signing
    (joint key reuse); game hops need a DDH oracle to handle
    signature-scheme reductions without knowing secret scalars.
  - Multi-session hybrids require repeated DDH checks.

## Simplifying assumption: fixed roles

Throughout this file we fix **Alice as the initiator** and **Bob
as the responder**, matching the structure of the passive file.
Every session in the AKE game is an Alice-init / Bob-resp
handshake; the reverse direction (Bob starts a chat with Alice)
is not explicitly modeled.

This is a valid simplification because:
  - Alice and Bob are labels for "the two honest parties" — by
    symmetry, a theorem proved for Alice=init/Bob=resp implies
    the same theorem for the swapped-label scenario.
  - No game hop in the standard AKE reduction (sig forgery →
    gapDH → ROM) requires role swapping. Each hop is local to
    the test session and can be carried out with fixed roles.
  - It keeps the skeleton close to the passive file's structure,
    avoiding a separate `SessionRole` type.

Future extensions that may want to relax this:
  - **Double Ratchet**: sessions have cross-direction
    interactions; role flexibility may become necessary.
  - **PQXDH with KEM**: although KEM encaps/decaps is also
    asymmetric, the same fixed-role simplification works;
    encaps = Alice, decaps = Bob. No extra type needed.
  - **Multi-party settings**: if we ever move beyond two
    honest parties, role tracking per session becomes essential.

## Reference

  Bhargavan, Jacomme, Kiefer, Schmidt.
  "Formal verification of the PQXDH Post-Quantum key agreement
   protocol for end-to-end secure messaging."
  USENIX Security 2024.
    - §2.4 (security properties), pp. 472
    - §3.2 (classical computational security), pp. 475
    - §5.2 (Theorem 2: active AKE security), pp. 479

See also `PQXDHLean/SecurityDefs.lean` for the `AKE_Query`,
`Freshness`, and hardness-assumption `Prop`s used below.
-/
import PQXDHLean.Tactics.PermDraws
import PQXDHLean.X3DH.X3DH
import PQXDHLean.SecurityDefs
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.SimSemantics.Append

open OracleComp OracleSpec

set_option autoImplicit false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {SK : Type} [Fintype SK] [DecidableEq SK] [SampleableType SK]

/-! ## AKE adversary model

See `SecurityDefs.AKE_Query` for the five query types
(`NewSession`, `Send`, `Corrupt`, `RevealSessionKey`, `Test`).

Informally, an active adversary is an interactive algorithm
that makes these queries in sequence, observing each response
before choosing its next query. At the end it outputs a single
`Bool` — its guess for the test query's hidden bit.

The contrast with passive:
  - Passive adversary: receives a fixed public transcript +
    candidate session key once; returns `Bool`.
  - Active adversary: participates in the protocol execution
    interactively, choosing which sessions to probe and which
    compromise events to trigger. -/

/-! ## Session state

**Notation convention** (shared with `X3DH.lean`):
  - Lowercase field names (`ek`, `spk`, `opk`) denote **private**
    scalars in `F`.
  - Uppercase prefixes (`IK`, `SPK`, `OPK`, `EK`) denote **public**
    group elements in `G`.
  - The `recv_*` prefix marks values that were *received over the
    network* — under active attack these may not match the named
    party's actual key material; they are whatever the adversary
    delivered. Authenticity is checked downstream (signatures,
    AEAD integrity). -/

/-- Unique identifier for a protocol session.

NOTE: Consider making this abstract (`{SID : Type} [DecidableEq SID]`)
during refinement if implementation-agnosticism becomes important.
For the skeleton, `Nat` is concrete and keeps type parameters minimal. -/
abbrev SessionId := Nat

/-- Handshake status of a session.

  * `pending` — session was started but the handshake has not
    yet completed
  * `accepted` — handshake completed successfully; a session key
    has been derived and is stored in the record
  * `rejected` — handshake aborted (e.g., signature verification
    failed, AEAD decryption failed)
-/
inductive SessionStatus where
  | pending
  | accepted
  | rejected
  deriving DecidableEq, Inhabited

/-- Stub for X3DH protocol messages, exchanged via the `send`
oracle and stored in session `transcript`s. Kept abstract for
the time being.

TODO (future refinement): replace with a concrete inductive type
carrying the actual X3DH message fields. The two message kinds
exchanged are:

```
inductive X3DHMessage (G CT_aead S_sig : Type) where
  /-- Bob's prekey bundle (published, fetched by Alice). -/
  | prekeyBundle (IK SPK : G) (OPK : Option G)
                 (sig_SPK : S_sig) (sig_OPK : Option S_sig)
  /-- Alice's initial AEAD ciphertext to Bob. -/
  | initCiphertext (EK : G) (spk_id : Nat) (opk_id : Option Nat)
                   (ct : CT_aead)
```

The skeleton uses `Unit` so `akeSpec` and the session records
typecheck without committing to message structure yet. -/
abbrev X3DHMessage := Unit

/-- Alice's view of one X3DH handshake (initiator side).

Under our fixed-roles convention, every session has Alice as the
initiator. This record captures what Alice locally knows about
the session: her fresh ephemeral private scalar, the peer's
prekey-bundle values as she received them, and her current
handshake status.

The `recv_*` fields are values Alice received from the network.
In an honest run they match Bob's actual keys; in an active
attack they may have been substituted by the adversary. Their
authenticity is checked downstream (signature verification on
the prekey bundle, AEAD integrity on the eventual response).

Following Bhargavan et al. §2.3 (Figure 1, p. 471): Alice samples
`ek ←$ F`, fetches `(IK, SPK, OPK?)` from the server, computes
the four DH values, derives `SK` via KDF, and encrypts her first
message with AEAD using `AD = (IK_a, IK_b)`. -/
structure AliceSessionRecord (F G SK : Type _) where
  /-- Unique identifier for this session. -/
  sid : SessionId
  /-- Alice's fresh ephemeral private scalar, sampled when the
  session was created. The corresponding public value
  `EK = ek • G₀` is derivable from this. -/
  ek : F
  /-- Peer's identity public key, as received over the network.
  `none` while the session is `pending` (no bundle received yet);
  becomes `some IK` once the prekey bundle has been delivered.
  May not equal Bob's actual `IK_b` if the adversary tampered. -/
  recv_IK : Option G
  /-- Peer's signed prekey public, as received. `none` while
  pending; set together with `recv_IK` when the bundle arrives. -/
  recv_SPK : Option G
  /-- Peer's one-time prekey public, as received. `none` either
  because the bundle hasn't arrived yet, or because the server
  had no OPK available (the protocol allows this). Disambiguate
  via `status` together with `recv_IK.isSome`. -/
  recv_OPK : Option G
  /-- Current handshake status. -/
  status : SessionStatus
  /-- Derived session key. Invariant: `sessionKey.isSome ↔
  status = SessionStatus.accepted`. -/
  sessionKey : Option SK
  /-- Ordered list of `X3DHMessage`s this session has observed
  (sent or received), in the order they occurred. Used for
  partnering / matching-session checks: two sessions are
  partnered iff their transcripts are compatible (Alice's sent
  message equals Bob's received message, etc.). The exact
  partnering predicate is TODO; this field is just the data
  it will operate on. -/
  transcript : List X3DHMessage

/-- Bob's view of one X3DH handshake (responder side).

Under our fixed-roles convention, every session has Bob as the
responder. This record captures what Bob locally knows about
the session: which of his prekey scalars were consumed, what
he received in Alice's initial message, and his current status.

The `recv_*` fields are values Bob received from the network.
The adversary may have crafted them. Bob verifies them via the
AEAD integrity check using the derived session key.

Following Bhargavan et al. §2.3 (Figure 1, p. 471): Bob has
previously published `(IK, SPK, OPK?)` to the server (with
signatures). When Alice's initial message arrives, Bob identifies
which `(SPK, OPK?)` were used (via the message's key ids),
runs the four DH computations, derives `SK`, and attempts AEAD
decryption. -/
structure BobSessionRecord (F G SK : Type _) where
  /-- Unique identifier for this session. -/
  sid : SessionId
  /-- The SPK private scalar Bob used in this session. SPKs may
  be reused across sessions until rotated. -/
  spk : F
  /-- The OPK private scalar Bob used, if any. OPKs are
  single-use; `none` means no OPK was consumed for this session. -/
  opk : Option F
  /-- Peer's identity public key, as received over the network.
  `none` while the session is `pending` (no initial message
  received yet); becomes `some IK` once Alice's initial message
  has been delivered. May not equal Alice's actual `IK_a` if
  the adversary tampered. -/
  recv_IK : Option G
  /-- Peer's ephemeral public key, as received. `none` while
  pending; set together with `recv_IK` when the initial message
  arrives. -/
  recv_EK : Option G
  /-- Current handshake status. -/
  status : SessionStatus
  /-- Derived session key. Invariant: `sessionKey.isSome ↔
  status = SessionStatus.accepted`. -/
  sessionKey : Option SK
  /-- Ordered list of `X3DHMessage`s this session has observed
  (sent or received), in the order they occurred. Used for
  partnering / matching-session checks. See the corresponding
  comment on `AliceSessionRecord.transcript`. -/
  transcript : List X3DHMessage

/-- The AKE game state.

Holds everything the challenger needs to track across the
adversary's interactive queries:

  * **Two session tables** (Alice's view and Bob's view), indexed
    by `SessionId`. SIDs are globally unique and partitioned: a
    given SID is in exactly one of the tables (whichever party
    started the session via `NewSession`).
  * **A counter `nextSid`** for allocating fresh session ids.
  * **Per-party corruption flags** indicating whether each
    party's long-term identity key has leaked via `Corrupt`.
  * **A revealed set** (characteristic function) listing session
    ids whose session keys have leaked via `RevealSessionKey`.
  * **An optional test session** identifying which session was
    chosen as the target of the (single) `Test` query.

The hidden test bit is not part of this state — under our
two-game formulation (`activeReal` / `activeRand`), the
real-vs-random choice is determined by which game variant is
running, not by an internal coin flip.

TODO (future refinement, needed for forward secrecy):
  * Replace boolean corruption flags with `Option Nat`
    timestamps so the freshness condition
    `no_dual_corruption_before_completion` can compare against
    each session's acceptance time.
  * Add an `acceptedAt : Option Nat` field to the session records
    (and a global `clock : Nat` here) for the same reason.
  * Add a partnering relation on transcripts (requires the
    `transcript` field on session records). -/
structure ActiveGameState (F G SK : Type _) where
  /-- Alice's session records, indexed by `SessionId`. `none`
  for ids not allocated as Alice sessions. -/
  aliceSessions : SessionId → Option (AliceSessionRecord F G SK)
  /-- Bob's session records, indexed by `SessionId`. `none`
  for ids not allocated as Bob sessions. -/
  bobSessions : SessionId → Option (BobSessionRecord F G SK)
  /-- Next free session id. `NewSession` allocates this and
  increments by one.

  Operational invariant (maintained by `newSessionImpl`, not
  enforced at the type level): for all `sid ≥ nextSid`,
  both `aliceSessions sid = none` and `bobSessions sid = none`. -/
  nextSid : SessionId
  /-- `true` iff Alice's long-term identity key has been
  released via a `Corrupt` query. -/
  aliceCorrupted : Bool
  /-- `true` iff Bob's long-term identity key has been
  released via a `Corrupt` query. -/
  bobCorrupted : Bool
  /-- Characteristic function of the set of session ids whose
  session keys have been released via `RevealSessionKey`. -/
  sk_revealed : SessionId → Bool
  /-- The session id designated by the (single) `Test` query.
  `none` before `Test` is called; `some sid` afterwards. -/
  testSession : Option SessionId

/-- Initial empty game state: no sessions, no corruption, no
reveals, no test query. Games begin in this state. -/
def ActiveGameState.empty {F G SK : Type _} : ActiveGameState F G SK where
  aliceSessions := fun _ => none
  bobSessions := fun _ => none
  nextSid := 0
  aliceCorrupted := false
  bobCorrupted := false
  sk_revealed := fun _ => false
  testSession := none

instance {F G SK : Type _} : Inhabited (ActiveGameState F G SK) :=
  ⟨ActiveGameState.empty⟩

/-! ## Active adversary

Following Bhargavan et al. §5.2 (p. 479), an active AKE adversary
is an interactive probabilistic algorithm that issues queries to
the challenger, observes responses, and eventually outputs a
single `Bool` — its guess for the test session's hidden bit.

We model it as an `OracleComp` over a combined oracle spec:
  - `unifSpec` — internal uniform sampling
  - `akeSpec` — the five AKE queries (`NewSession`, `Send`,
    `Corrupt`, `RevealSessionKey`, `Test`)
  - `KDFOracle` — the random-oracle KDF (per
    `SecurityDefs.KDF_RandomOracle`) -/

/-- One of the two honest parties in our fixed-roles game.
Used as the input type for queries that select a party
(`Corrupt`, `NewSession`). -/
inductive Party where
  | alice
  | bob
  deriving DecidableEq

/-- The five AKE oracle queries, with their inputs embedded.

In VCVio, an `OracleSpec ι` is a function `ι → Type` mapping
each query (the *index*) to its response type. We model the AKE
queries as constructors of this inductive: each constructor
carries the adversary's input, and `akeSpec` (below) tells us
the response type for each.

Mirrors `SecurityDefs.AKE_Query`, specialized to our fixed-roles
setup (role information is implicit in the `Party` argument). -/
inductive AKEQuery where
  /-- Start a new session on the named party's side. -/
  | newSession (party : Party)
  /-- Deliver a (possibly tampered) message to a session. -/
  | send (sid : SessionId) (msg : X3DHMessage)
  /-- Release a party's long-term identity secret key. -/
  | corrupt (party : Party)
  /-- Release a completed session's session key. -/
  | revealSK (sid : SessionId)
  /-- The challenge query (once per game). -/
  | test (sid : SessionId)

/-- Oracle specification for the AKE adversary's interactive
queries.

In VCVio, an `OracleSpec ι` is a function `ι → Type` from query
indices to response types. Each constructor of `AKEQuery` is one
query (with its input embedded); `akeSpec F SK` maps each
constructor to its response type.

Concrete implementations of these queries are provided as
`QueryImpl`s in the *Oracle implementations* section below. -/
def akeSpec (F SK : Type) : OracleSpec AKEQuery := fun
  | .newSession _ => SessionId
  | .send _ _ => Option X3DHMessage
  | .corrupt _ => F
  | .revealSK _ => Option SK
  | .test _ => Option SK

/-- An active AKE adversary against X3DH.

An interactive probabilistic algorithm with access to three
oracle specs combined by `+`:
  * `unifSpec` — internal uniform sampling
  * `akeSpec F SK` — the five AKE queries
  * `KDFOracle (G × G × G × G) SK` — the random-oracle KDF

It outputs a single `Bool` — its guess for the test session's
hidden bit. Unlike the passive adversary (which receives a fixed
public transcript and returns once), the active adversary chooses
its own queries and observes responses one at a time, with the
challenger's game state evolving across the interaction. -/
abbrev ActiveAdversary (F G SK : Type) :=
  OracleComp (unifSpec + akeSpec F SK + KDFOracle (G × G × G × G) SK) Bool

/-! ## Oracle implementations

Each of the five AKE queries (`AKEQuery` constructors) is
realized by a handler running in `AKEStateM` — a state monad
threading `ActiveGameState` over the rest of the adversary's
oracle stack (uniform sampling + the KDF random oracle).

The unified `akeQueryImpl` pattern-matches on `AKEQuery` and
dispatches to the appropriate handler.

Long-term keys (`ikₐ`, `ikᵦ`, `spkᵦ` — lowercase = private, with
party subscript ₐ/ᵦ following the passive file's convention) are
passed as parameters rather than stored in `ActiveGameState`,
since they are sampled once at game setup and never change during
the interactive phase. -/

/-- The state monad each oracle handler lives in. Threads
`ActiveGameState` over an `OracleComp` that exposes uniform
sampling (for fresh ephemerals) and the KDF random oracle. -/
abbrev AKEStateM (F G SK : Type) :=
  StateT (ActiveGameState F G SK)
    (OracleComp (unifSpec + KDFOracle (G × G × G × G) SK))

/-- Unified `QueryImpl` for the AKE oracle spec.

Pattern matches on `AKEQuery` and dispatches to per-query logic.
Some handlers are implemented inline; the more complex ones
(`newSession`, `send`, `test`) are stubbed with `sorry` and
detailed TODO comments documenting what each must do.

Parameters:
  * `ikₐ`, `ikᵦ` — long-term identity private keys
  * `spkᵦ` — Bob's signed-prekey private (reused across his
    sessions until rotated; we model a single rotation in this
    skeleton)
  * `getTestKey` — callback supplying the response for the
    `test` query. The two-game formulation (`activeReal` /
    `activeRand`) instantiates this differently:
      - real game: `fun sk => return sk` (pass the actual key)
      - random game: `fun _ => liftM ($ᵗ SK)` (sample fresh) -/
noncomputable def akeQueryImpl
    (ikₐ ikᵦ spkᵦ : F)
    (getTestKey : SK → AKEStateM F G SK SK) :
    QueryImpl (akeSpec F SK) (AKEStateM F G SK) := fun
  | .newSession party => do
      -- Create a new session record in `pending` state, allocate
      -- a fresh `SessionId`, and insert into the appropriate
      -- per-party table.
      --
      -- For Alice: sample a fresh ephemeral scalar `ek` and
      -- record it. The peer-key fields stay `none` until the
      -- prekey bundle is later delivered via `Send`.
      --
      -- For Bob: sample a fresh one-time-prekey scalar `opk`.
      -- The signed-prekey scalar `spk` is shared (passed to
      -- `akeQueryImpl`). The peer-key fields stay `none` until
      -- Alice's initial message is later delivered via `Send`.
      let s ← get
      let sid := s.nextSid
      match party with
      | .alice =>
          let ek ← liftM ($ᵗ F)
          let rec_a : AliceSessionRecord F G SK :=
            { sid := sid, ek := ek
              recv_IK := none, recv_SPK := none, recv_OPK := none
              status := .pending, sessionKey := none
              transcript := [] }
          modify fun s =>
            { s with
              nextSid := s.nextSid + 1
              aliceSessions := fun i =>
                if i = sid then some rec_a else s.aliceSessions i }
          return sid
      | .bob =>
          let opk ← liftM ($ᵗ F)
          let rec_b : BobSessionRecord F G SK :=
            { sid := sid, spk := spkᵦ, opk := some opk
              recv_IK := none, recv_EK := none
              status := .pending, sessionKey := none
              transcript := [] }
          modify fun s =>
            { s with
              nextSid := s.nextSid + 1
              bobSessions := fun i =>
                if i = sid then some rec_b else s.bobSessions i }
          return sid
  | .send _sid _msg => by
      -- TODO: deliver a (possibly tampered) message to a session.
      --
      -- This is the most complex handler — it implements the
      -- protocol's state machine. Roughly:
      --
      --   1. Look up the session in `aliceSessions` or `bobSessions`.
      --      Fail (return `none`) if not found or not `pending`.
      --
      --   2. Parse the incoming `X3DHMessage` (currently `Unit`,
      --      pending refinement). Two valid cases:
      --
      --        (a) Alice's session expects a `prekeyBundle`:
      --              - Verify `sig_SPK` against the claimed `IK`
      --                (reduction target for `Sig_EUF_CMA`).
      --              - Verify `sig_OPK` if `OPK` is present.
      --              - On success: store `recv_IK`, `recv_SPK`,
      --                `recv_OPK` in the session. Compute the
      --                four DH values via `X3DH_Alice`, derive
      --                `SK := kdf.derive (DH₁,DH₂,DH₃,DH₄)`,
      --                store `sessionKey := some SK`, set
      --                `status := .accepted`. Return a freshly-
      --                constructed `initCiphertext` as outgoing.
      --              - On failure: set `status := .rejected`,
      --                return `none`.
      --
      --        (b) Bob's session expects an `initCiphertext`:
      --              - Store `recv_IK`, `recv_EK`. Compute DH
      --                values via `X3DH_Bob`, derive `SK`,
      --                attempt AEAD decryption.
      --              - On success: set `status := .accepted`,
      --                store `sessionKey`, return `none`.
      --              - On failure: set `status := .rejected`.
      --
      --   3. Anything else (mismatched message kind, invalid
      --      session): set `status := .rejected`, return `none`.
      --
      -- Implementing this requires concretizing `X3DHMessage`
      -- and choosing how signatures + AEAD are threaded.
      exact sorry
  | .corrupt party => do
      -- Release the named party's long-term identity key. Mark
      -- the corruption in state; future freshness checks will
      -- use this flag.
      modify fun s => match party with
        | .alice => { s with aliceCorrupted := true }
        | .bob => { s with bobCorrupted := true }
      return (match party with | .alice => ikₐ | .bob => ikᵦ)
  | .revealSK sid => do
      -- Release the named session's session key, if it exists
      -- and the session has accepted. Mark the reveal in state.
      let s ← get
      let aliceK := (s.aliceSessions sid).bind (·.sessionKey)
      let bobK := (s.bobSessions sid).bind (·.sessionKey)
      let key := aliceK <|> bobK
      if key.isSome then
        modify fun s =>
          { s with sk_revealed := fun i => i = sid || s.sk_revealed i }
      return key
  | .test sid => do
      -- The challenge query. At most one Test per game.
      --
      -- Partial implementation: handles the once-per-game check,
      -- session lookup, and dispatch to `getTestKey`. Full
      -- freshness checks are still TODO (they require partnering
      -- via `transcript` fields, which are deferred).
      let s ← get
      if s.testSession.isSome then
        -- Test already invoked; refuse.
        return none
      -- TODO: full freshness checks
      --   * `state.sk_revealed sid = false`
      --   * the partner session's key not revealed (requires
      --     partnering — see `SessionRecord` `transcript` TODO)
      --   * `¬ (state.aliceCorrupted ∧ state.bobCorrupted)` (or
      --     a stronger pre-completion variant when timestamps
      --     are added)
      let aliceK := (s.aliceSessions sid).bind (·.sessionKey)
      let bobK := (s.bobSessions sid).bind (·.sessionKey)
      let realKey := aliceK <|> bobK
      match realKey with
      | none =>
          -- Session not accepted (or doesn't exist) — can't test.
          return none
      | some sk =>
          modify fun state => { state with testSession := some sid }
          let r ← getTestKey sk
          return (some r)

/-! ## Active secrecy games (real and random)

Parallels the two-game structure from the passive file:
  - `activeReal`: adversary plays full AKE game, Test returns real key
  - `activeRand`: same, but Test returns a fresh uniform key

The distinguishing advantage between these two games is the
quantity the reduction bounds. -/

/-- Common AKE game scaffold, parameterized by the `getTestKey`
callback that determines `Test`'s response.

Implementation flow:
  1. Sample long-term keys (`ikₐ`, `ikᵦ`, `spkᵦ`) at the outer
     `OracleComp` layer via `$ᵗ F`.
  2. Build the AKE handler `akeImpl := akeQueryImpl ikₐ ikᵦ spkᵦ
     getTestKey`.
  3. Build pass-through handlers for `unifSpec` and `KDFOracle`
     into `AKEStateM` via `QueryImpl.ofLift` + `liftTarget`.
     These forward queries to the inner `OracleComp` layer where
     they are processed by step 6's outer interpretation.
  4. Combine the three handlers with `+` and `simulateQ` the
     adversary against the combined impl, producing a value in
     `AKEStateM F G SK Bool`.
  5. `StateT.run'` with `ActiveGameState.empty` discards the
     final game state, leaving an `OracleComp (unifSpec +
     KDFOracle ...) Bool`.
  6. Interpret the remaining `unifSpec + KDFOracle` queries into
     `ProbComp` exactly as passive's `execGame` does
     (`X3DHPassiveMessageSecrecy.lean`). -/
private noncomputable def activeGame
    (adv : ActiveAdversary F G SK)
    (getTestKey : SK → AKEStateM F G SK SK) :
    ProbComp Bool :=
  -- Steps 1-5: sample keys, simulate adversary in AKEStateM,
  -- strip the StateT layer to land in OracleComp.
  let outer : OracleComp (unifSpec + KDFOracle (G × G × G × G) SK) Bool := do
    let ikₐ ← $ᵗ F
    let ikᵦ ← $ᵗ F
    let spkᵦ ← $ᵗ F
    let akeImpl : QueryImpl (akeSpec F SK) (AKEStateM F G SK) :=
      akeQueryImpl ikₐ ikᵦ spkᵦ getTestKey
    let unifImpl : QueryImpl unifSpec (AKEStateM F G SK) :=
      (QueryImpl.ofLift unifSpec
          (OracleComp (unifSpec + KDFOracle (G × G × G × G) SK))).liftTarget _
    let kdfImpl :
        QueryImpl (KDFOracle (G × G × G × G) SK) (AKEStateM F G SK) :=
      (QueryImpl.ofLift (KDFOracle (G × G × G × G) SK)
          (OracleComp (unifSpec + KDFOracle (G × G × G × G) SK))).liftTarget _
    StateT.run' (simulateQ (unifImpl + akeImpl + kdfImpl) adv)
                ActiveGameState.empty
  -- Step 6: interpret remaining queries into ProbComp, exactly
  -- as passive's `execGame` does.
  let kdfImplPC : QueryImpl (KDFOracle (G × G × G × G) SK) ProbComp :=
    fun _ => $ᵗ SK
  let idImplPC : QueryImpl unifSpec ProbComp :=
    QueryImpl.ofLift unifSpec ProbComp
  simulateQ (idImplPC + kdfImplPC) outer

/-- Real-key active game. The `Test` query returns the session's
actual derived key. -/
noncomputable def activeReal
    (adv : ActiveAdversary F G SK) : ProbComp Bool :=
  activeGame adv (fun sk => return sk)

/-- Random-key active game. The `Test` query returns a fresh
uniform sample from `SK`, independent of the actual session
key. -/
noncomputable def activeRand
    (adv : ActiveAdversary F G SK) : ProbComp Bool :=
  activeGame adv (fun _ => liftM ($ᵗ SK))

/-! ## Advantage -/

/-- Distinguishing advantage of an active adversary in the AKE
game. Mirrors `passiveSecrecyAdvantage` from
`X3DHPassiveMessageSecrecy.lean`:

```
advantage := |Pr[true | activeReal] - Pr[true | activeRand]|
```

Security under the paper's Theorem 2 (§5.2) means: for every
fresh adversary, this advantage is bounded by the sum of the
adversary's advantages against the underlying assumptions
(gapDH, ROM/PRF KDF, AEAD IND-CPA + INT-CTXT, Sig EUF-CMA). -/
noncomputable def activeSecrecyAdvantage
    (adv : ActiveAdversary F G SK) : ℝ :=
  ProbComp.boolDistAdvantage (activeReal adv) (activeRand adv)

/-! ## Security target (opaque)

`SecurityDefs.MessageSecrecy` is parameterized over a KEM.
X3DH has no KEM component, so we declare a KEM-free variant
here. Follow-up work will either:
  (a) lift this into `SecurityDefs.lean` alongside the existing
      `MessageSecrecy`, or
  (b) unify by instantiating the KEM with trivial types.
-/

/-- TODO: active message secrecy for X3DH (no KEM component).
Placeholder — semantically identical to `MessageSecrecy` from
`SecurityDefs.lean` with the KEM arguments dropped. -/
opaque X3DH_ActiveMessageSecrecy
    (G : Type _) [AddCommGroup G]
    (I K : Type _) (_kdf : KDF I K)
    (_fresh : Freshness) : Prop

/-! ## Security theorem -/

-- The `[Fintype SK]`, `[DecidableEq G]`, `[DecidableEq SK]`
-- instances below are unused until the proof body is filled in
-- (they become needed once `activeSecrecyAdvantage` is concrete
-- and probability equalities are being reasoned about).
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- X3DH active message secrecy under the classical assumptions.

Paper reference: Bhargavan et al. Theorem 2 (§5.2), restricted
to the X3DH sub-protocol.

Under:
  - gapDH hardness (stronger than DDH — needed for multi-session
    hybrids and joint DH/signing-key reuse in XEdDSA)
  - KDF modeled as Random Oracle
  - AEAD is IND-CPA + INT-CTXT
  - Signature scheme (XEdDSA) is EUF-CMA

the session key derived by a fresh test session is
indistinguishable from a uniformly random key. -/
theorem x3dh_active_message_secrecy
    {G₀ : G} {PT CT_aead PK_sig SK_sig M S_sig : Type _}
    (kdf : KDF (G × G × G × G) SK)
    (aead : AEAD SK PT CT_aead (G × G))
    (sig : Sig PK_sig SK_sig M S_sig)
    (fresh : Freshness)
    (_h_gapdh : GapDH_Hard G G₀)
    (_h_kdf_ro : KDF_RandomOracle (G × G × G × G) SK kdf)
    (_h_aead : AEAD_IND_CPA_INT_CTXT SK PT CT_aead (G × G) aead)
    (_h_sig : Sig_EUF_CMA PK_sig SK_sig M S_sig sig) :
    X3DH_ActiveMessageSecrecy G (G × G × G × G) SK kdf fresh := by
  sorry

/-! ## Corollary: passive security is a special case

A passive adversary is an active adversary that never uses
`Send`, `Corrupt`, or `RevealSessionKey`. The theorem below
(when proved) would let us derive `passive_secrecy_le_ddh`
as a corollary — establishing a single source of truth for
X3DH secrecy. -/

/-- TODO: every `PassiveAdversary` embeds as an `ActiveAdversary`
that ignores the `Send`/`Corrupt`/`RevealSessionKey` oracles. -/
theorem passive_embeds_into_active :
    True := by
  sorry

/-! ## Follow-up work

This section tracks remaining gaps. Status markers:
  ✓ done, 🚧 partial, ☐ pending. Roughly in dependency order.

### 1. Session state design 🚧 Mostly done

Done:
  - `SessionStatus` enum (`pending` | `accepted` | `rejected`)
  - `AliceSessionRecord` / `BobSessionRecord` (per-side, with
    fixed roles; `recv_*` peer-key fields are `Option G` to
    distinguish "not yet received" from "received and was X")
  - `transcript : List X3DHMessage` field on each record —
    initialized to `[]` by `newSession`; future `send` will
    append to it as messages flow through the session
  - `ActiveGameState` — session tables, corruption flags,
    `sk_revealed`, `testSession`
  - `ActiveGameState.empty` and `Inhabited` instance

Still TODO:
  - **Partnering predicate** — define a concrete
    `arePartners : AliceSessionRecord → BobSessionRecord → Prop`
    relating two sessions whose transcripts and observed
    peer keys are consistent. Needed by the partner-reveal
    freshness check (§6).
  - **Timestamps** for corruption (`Bool` → `Option Nat`) if
    forward-secrecy proofs need pre-completion timing.
  - **Consider abstracting** `SessionId` via type parameter
    (currently `Nat`) — minor refinement, see TODO at the
    declaration.

### 2. Oracle implementations 🚧 3/5 done

Implemented inline in `akeQueryImpl`:
  - `corrupt` ✓ — flips party's `Corrupted` flag, returns
    its long-term IK private scalar
  - `revealSK` ✓ — looks up session in either table, returns
    `sessionKey` if accepted, marks `sk_revealed`
  - `newSession` ✓ — samples fresh ephemeral (Alice) or fresh
    OPK (Bob), allocates `sid` from `nextSid`, inserts record
    with `recv_*` fields as `none` and `status := pending`

Partial:
  - `test` 🚧 — once-per-game guard, session lookup, and
    `getTestKey` dispatch are implemented. Still TODO:
    full freshness checks (`sk_revealed`, partner reveal,
    dual corruption) — partner check needs transcripts (§1).

Pending (`sorry`):
  - `send` ☐ — biggest remaining handler. Needs:
    * Concrete `X3DHMessage` (currently `Unit`) with
      `prekeyBundle` and `initCiphertext` constructors
    * `Sig` and `AEAD` parameters threaded through `akeQueryImpl`
    * `KDF` parameter (or use the ROM oracle directly via
      `query (Sum.inr ...)`)
    * Protocol state machine: parse → branch by side → verify
      signatures → compute DH via `X3DH_Alice` / `X3DH_Bob` →
      derive SK → encrypt-or-decrypt → update record status
    * Estimated 200-300 LOC; see the inline TODO and the
      requirements list discussed in code review

### 3. Adversary interactivity ✓ Done

  - `Party` enum (`alice` | `bob`)
  - `AKEQuery` inductive carrying inputs in its constructors
  - `akeSpec : OracleSpec AKEQuery` mapping queries to
    response types
  - `ActiveAdversary` =
    `OracleComp (unifSpec + akeSpec F SK + KDFOracle ...) Bool`

### 4. `simulateQ` wiring for `activeGame` ✓ Done

`activeGame` is fully implemented. The body:
  1. Samples `ikₐ`, `ikᵦ`, `spkᵦ ←$ F` at the outer `OracleComp`
     layer.
  2. Builds `akeImpl := akeQueryImpl ikₐ ikᵦ spkᵦ getTestKey`.
  3. Lifts `unifSpec` and `KDFOracle` query handlers into
     `AKEStateM` via `QueryImpl.ofLift` + `liftTarget`.
  4. Combines all three impls with `+` and `simulateQ`s the
     adversary, producing `AKEStateM Bool`.
  5. `StateT.run'` with `ActiveGameState.empty` strips the
     state, yielding `OracleComp (unifSpec + KDFOracle ...) Bool`.
  6. Interprets the remaining queries into `ProbComp` exactly
     as passive's `execGame` does (`unifSpec` passes through,
     `KDFOracle` becomes fresh-sample `$ᵗ SK`).

Consequence: `activeReal`, `activeRand`, and
`activeSecrecyAdvantage` are now executable definitions all the
way down (no `sorry`s in their dependencies, except for the
`send` handler within `akeQueryImpl` and the freshness branch
of `test`).

### 5. MessageSecrecy adapter 🚧 Local definition done

Done: declared `X3DH_ActiveMessageSecrecy` as a local opaque
`Prop` (no KEM parameter, since X3DH has none). The main
theorem uses it as its conclusion.

Still TODO: lift `X3DH_ActiveMessageSecrecy` into
`SecurityDefs.lean` so it sits alongside the existing
`MessageSecrecy` (PQXDH-style) and `PeerAuth` properties.
Small refactor; could be a self-contained PR.

### 6. Freshness validation ☐ Pending

`SecurityDefs.Freshness` has three opaque `Prop` fields:
  - `no_reveal_test`
  - `no_reveal_partner`
  - `no_dual_corruption_before_completion`
Replace each with a concrete predicate over `ActiveGameState`
and the test `SessionId`. This unblocks the full `test`
implementation (§2) and makes the main theorem's `Freshness`
hypothesis meaningful.

The partner-reveal predicate depends on partnering, which
requires transcripts (§1).

### 7. Game-hop proof for the main theorem ☐ Pending — main effort

Build the reduction chain. Each step uses VCVio's identical-
until-bad lemma `tvDist_simulateQ_le_probEvent_bad`:

    G₀ — real AKE game
    ↓   [bad event: adversary forges a signature on honest party's key]
    ↓   bound: Sig EUF-CMA advantage (via `SignatureAlg.unforgeableExp`)
    G₁ — signatures verified against lookup table
    ↓   [bad event: adversary guesses DH output on a fresh session]
    ↓   bound: gapDH advantage
    G₂ — DH values randomized in fresh sessions
    ↓   [bad event: adversary queries KDF on the real DH tuple]
    ↓   bound: ROM advantage (controlled via cache inspection)
    G₃ — session keys uniformly random in test session
    ↓
    G₄ — pure random; adversary advantage = 0

Total advantage bound:
    activeSecrecyAdvantage adv
      ≤ SigEUFCMA_adv(B_sig) + GapDH_adv(B_gapDH)
        + KDF_ROM_adv(B_kdf) + AEAD_adv(B_aead)

Filling in this proof depends on §2 (full `send` / `test`),
§4 (`simulateQ` wiring), and §6 (freshness predicates).

### 8. Query bounding ☐ Pending

Concrete security bounds depend on the number of queries the
adversary makes. Use `OracleComp.IsQueryBound` to constrain:
  - `Q_newSession`, `Q_send`, `Q_corrupt`, `Q_revealSK`
  - Final bound will be polynomial in these.
Without a query bound, the theorem can only say "advantage is
negligible" — which is fine as a first pass but weaker than
concrete bounds.

### 9. Passive-embeds-into-active corollary ☐ Pending

Prove `passive_embeds_into_active`: every `PassiveAdversary`
can be lifted to an `ActiveAdversary` that uses only `Test`
(no `Send`, `Corrupt`, `RevealSessionKey`). Then derive
`passive_secrecy_le_ddh` (from `X3DHPassiveMessageSecrecy.lean`)
as a corollary of `x3dh_active_message_secrecy`. This unifies
the secrecy story.

### 10. Automation ☐ Pending

The `perm_draws` tactic was sufficient for the passive proof's
one-shot draw reordering. Active proofs are much larger:
  - Multiple game hops, each with its own simulation invariant
  - Cache-state reasoning (for the ROM)
  - Signature-log bookkeeping (for EUF-CMA reductions)
Likely need:
  - Heavier use of VCVio's `by_upto`, `rvcstep`, `rvcgen`
  - Possibly a new custom tactic for game-hop composition
  - Better simp sets for AKE-game normalization

### 11. Expansion to other security properties ☐ Pending

Once active secrecy lands, extend to the remaining four
properties from the paper's Theorem 2 / Theorem 1:
  - **Peer authentication** (`PeerAuth`) — if Bob accepts with
    apparent partner Alice, then Alice also ran the session.
    Proof reduces to Sig EUF-CMA.
  - **Forward secrecy** (`ForwardSecrecy`) — past sessions
    remain secure even if long-term keys leak later. Proof
    exploits ephemeral-key deletion.
  - **KCI resistance** (`KCI_Resistance`) — corrupting Alice's
    IK doesn't help impersonate Bob to her. Follows from the
    fact that authenticating Bob requires Bob's IK.
  - **Session independence** (`SessionIndependence`) — one
    session's key reveal doesn't compromise others. Follows
    from independent ephemeral samples.

Each property deserves its own file in `PQXDHLean/X3DH/`,
following the same skeleton structure. -/
