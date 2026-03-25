/-
Security definitions for the PQXDH main result.

Formalizes the cryptographic assumptions, adversary models, and
security games from:

  Bhargavan, Jacomme, Kiefer, Schmidt.
  "Formal verification of the PQXDH Post-Quantum key agreement
   protocol for end-to-end secure messaging."
  USENIX Security 2024.

## Design notes

Security properties in cryptography are defined relative to a
*security game* played between a challenger (running the protocol
honestly) and an adversary (who tries to break the security
guarantee). Each game specifies:

  1. What the challenger sets up (keys, sessions).
  2. What oracle queries the adversary may make (corrupt keys,
     reveal session keys, deliver/modify messages).
  3. What the adversary must achieve to "win" (distinguish a
     real key from random, forge a signature, etc.).
  4. A *freshness condition* that rules out trivial wins.

A scheme is secure if no efficient adversary wins with
non-negligible advantage. Since Lean cannot express computational
complexity bounds, we model each hardness assumption as an opaque
`Prop` whose internal structure documents the game but whose
truth is axiomatically assumed when needed.

The paper uses two complementary verification approaches:
  - **Symbolic model (ProVerif):** Dolev-Yao adversary, perfect
    cryptography, trace-based properties (correspondence assertions).
  - **Computational model (CryptoVerif):** game-based reductions,
    advantage bounds, concrete assumptions on primitives.
-/
import PQXDHLean.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD
import PQXDHLean.KEM

/-! ## Signature scheme -/

/-- A key pair for a signature scheme, coupling a public verification
key with the corresponding signing key. -/
structure SigKeyPair (PK_sig SK_sig : Type _) where
  pk : PK_sig
  sk : SK_sig

/-- Abstract digital signature scheme (e.g. XEdDSA over Curve25519).
Parameterized by public key, secret key, message, and signature types.

Correctness requires that honestly generated signatures verify
under the matching public key. -/
structure Sig (PK_sig SK_sig M S : Type _) where
  keygen : SigKeyPair PK_sig SK_sig
  sign : SK_sig → M → S
  verify : PK_sig → M → S → Bool
  correctness : ∀ (m : M), verify keygen.pk m (sign keygen.sk m) = true

/-! ## Adversary models

The paper analyzes PQXDH under two adversary models:
  - A symbolic (Dolev-Yao) model for ProVerif analysis.
  - A computational (game-based) model for CryptoVerif analysis.
-/

/-- The Dolev-Yao adversary model (symbolic/ProVerif).

A marker type indicating the analysis is carried out in the symbolic
model, where:
  - The adversary controls the network (active MitM): it can
    intercept, inject, replay, and modify all messages.
  - Cryptographic primitives are **ideal black boxes** — the
    adversary cannot break encryption, forge signatures, or invert
    hashes except by using the appropriate key.
  - The adversary may compromise long-term keys at any time
    (adaptive corruption).

Security properties are expressed as **correspondence assertions**:
  "if event A occurred (e.g. Bob completed a session with Alice),
   then event B must have occurred (e.g. Alice initiated it)."

In the post-quantum extension, the adversary is additionally given
the power to **break DH** (compute discrete logs) at some point in
time, modeling a future quantum computer. Security of sessions
completed *before* this point is then analyzed.

Since all primitives are ideal, **no computational hardness
assumptions** appear as hypotheses in the symbolic model.
Theorem 1 depends only on the protocol logic. -/
inductive DolevYao where
  | mk

/-- Oracle queries available to the adversary in the computational
authenticated key exchange (AKE) security game. This models the
interface between the adversary and the challenger in CryptoVerif.

Reference: §3.2 of the paper (CryptoVerif game formulation). -/
inductive AKE_Query where
  /-- Initiate a new protocol session between two identified parties.
      Returns a session handle. -/
  | NewSession
  /-- Deliver a (possibly modified) message to a session, advancing
      the protocol state. Models an active network attacker. -/
  | Send
  /-- Obtain the long-term secret key of a named party.
      Models key compromise / corruption. -/
  | Corrupt
  /-- Obtain the session key of a completed session.
      Models compromise of session-specific secrets. -/
  | RevealSessionKey
  /-- Challenge query: receive either the real session key or a
      uniformly random key (determined by a hidden coin flip).
      The adversary must guess which. -/
  | Test

/-- Freshness condition for the AKE security game.

A test session is *fresh* if the adversary has not trivially obtained
the answer. Specifically, a session between Alice (initiator) and
Bob (responder) is fresh if:

  1. The adversary did not `RevealSessionKey` on the test session
     or its matching partner session.
  2. The adversary did not `Corrupt` *both* Alice's and Bob's
     long-term identity keys before the test session completed.
  3. (For forward secrecy) The adversary did not `Corrupt` the
     ephemeral key of the test session.

The exact freshness condition varies by theorem; the paper defines
it within each CryptoVerif game. -/
structure Freshness where
  /-- Test session key was not revealed. -/
  no_reveal_test : Prop
  /-- Partner session key was not revealed. -/
  no_reveal_partner : Prop
  /-- Not both long-term keys corrupted before session completion. -/
  no_dual_corruption_before_completion : Prop

/-! ## Cryptographic hardness assumptions (§2.5)

Each assumption models a specific security game. We define them as
opaque `Prop`s parameterized by the relevant primitive, with
documentation describing the game structure.
-/

/-- §2.5 Assumption 1.A: the gap Diffie-Hellman (gapDH) problem is
hard on X25519.

**Game:** The challenger samples a, b ←$ ℤ_q and gives the adversary
(G, [a]G, [b]G) plus access to a DDH oracle (which, on input
(U, V, W), returns whether W = DH(u, V) for the unknown u).
The adversary must compute [ab]G.

gapDH is stronger than CDH (the DDH oracle helps) but the protocol
proof requires it because CryptoVerif uses DDH-like transitions
internally. The concrete group is X25519 (Curve25519).

Security means: no efficient adversary computes the answer with
non-negligible probability. -/
opaque GapDH_Hard (G : Type _) [AddCommGroup G] (gen : G) : Prop

/-- §2.5 Assumption 1.B: the KEM is IND-CCA (indistinguishable under
chosen-ciphertext attack).

**Game:**
  1. Challenger runs (pk, sk) ← KEM.keygen.
  2. Challenger computes (ss₀, ct*) ← KEM.encaps(pk), samples ss₁ ←$ SS.
  3. Challenger flips coin b ∈ {0,1}, gives adversary (pk, ct*, ssᵦ).
  4. Adversary has access to a decapsulation oracle KEM.decaps(sk, ·)
     for any ciphertext ct ≠ ct*.
  5. Adversary outputs guess b'.

Security means: |Pr[b' = b] − 1/2| is negligible.
Concrete instantiation: Kyber-1024 (ML-KEM), secure under Module-LWE. -/
opaque KEM_IND_CCA (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS) : Prop

/-- §2.5 Assumption 2 (classical variant): the KDF is a Random Oracle.

**Model:** The KDF is replaced by a truly random function — for each
new input, the output is sampled uniformly at random; repeated queries
with the same input return the same output.

This is the standard ROM (Random Oracle Model) assumption used in
the classical CryptoVerif proof. It is stronger than PRF but allows
a tighter reduction.

Concrete instantiation: HKDF-SHA-256 (RFC 5869). -/
opaque KDF_RandomOracle (I K : Type _) (kdf : KDF I K) : Prop

/-- §2.5 Assumption 2 (post-quantum variant): the KDF is a PRF
(pseudorandom function).

**Game:**
  1. Challenger samples a key k ←$ K and flips coin b ∈ {0,1}.
  2. If b = 0, the oracle returns KDF.derive(k, ·).
     If b = 1, the oracle returns a truly random function f(·).
  3. Adversary queries the oracle adaptively and outputs guess b'.

Security means: |Pr[b' = b] − 1/2| is negligible.

The post-quantum CryptoVerif proof uses PRF instead of ROM because
CryptoVerif's post-quantum soundness result does not capture the
Quantum Random Oracle Model (QROM). PRF suffices for the
post-quantum secrecy guarantee. -/
opaque KDF_PRF (I K : Type _) (kdf : KDF I K) : Prop

/-- §2.5 Assumption 3: the AEAD scheme is IND-CPA + INT-CTXT.

This is a conjunction of two standard security notions:

**IND-CPA (indistinguishability under chosen-plaintext attack):**
  Adversary chooses two plaintexts; receives encryption of one
  (chosen by coin flip); must guess which. Security means the
  advantage is negligible.

**INT-CTXT (integrity of ciphertext):**
  Adversary has access to an encryption oracle; must produce a
  *new* valid ciphertext (one not output by the oracle). Security
  means the probability of success is negligible.

Together, IND-CPA + INT-CTXT imply IND-CCA2 (Bellare & Namprempre).

Concrete instantiation: AES-256-CBC + HMAC in Encrypt-Then-MAC mode. -/
opaque AEAD_IND_CPA_INT_CTXT (K PT CT AD : Type _) (aead : AEAD K PT CT AD) : Prop

/-- §2.5 Assumption 4: the signature scheme is EUF-CMA (existentially
unforgeable under chosen-message attack).

**Game:**
  1. Challenger runs (pk, sk) ← Sig.keygen, gives pk to adversary.
  2. Adversary adaptively queries a signing oracle Sign(sk, ·),
     receiving signatures on messages of its choice.
  3. Adversary outputs (m*, σ*) where m* was never queried.

Security means: Pr[Verify(pk, m*, σ*) = true] is negligible.

Concrete instantiation: XEdDSA over Curve25519. -/
opaque Sig_EUF_CMA (PK_sig SK_sig M S : Type _) (sig : Sig PK_sig SK_sig M S) : Prop

/-- Temporal qualification for a cryptographic assumption: the
assumption held **at the time the key exchange completed**, but
may have been broken since (e.g. by a quantum computer).

In Theorem 3, the paper requires that the signature scheme was
EUF-CMA at the time Alice and Bob ran the protocol. The adversary
may later gain the ability to forge signatures (via a quantum
computer), but this does not retroactively compromise sessions
that were already established under valid signatures.

We distinguish this from the atemporal `Sig_EUF_CMA` used in
Theorem 2, where the assumption is required to hold throughout. -/
opaque HeldAtExchange (assumption : Prop) : Prop

/-! ## Semi-honest collision resistance (Definition 1, §4)

A new KEM security property introduced by the paper to address
the KEM re-encapsulation attack discovered in PQXDH v1.

### Motivation

In PQXDH, the server stores Bob's KEM public key (PQSPK). A
malicious server could replace Bob's PQSPK with a different key
pk' while keeping Bob's secret key sk unchanged. If the KEM allows
two different ciphertexts (under different public keys) to decapsulate
to the same shared secret under sk, the server can mount a
man-in-the-middle attack without detection.

SH-CR ensures this cannot happen: any ciphertext that decapsulates
correctly under sk must be the one honestly generated for the
matching public key.
-/

/-- Definition 1 (§4): Semi-Honest Collision Resistance (SH-CR).

**Game (2 phases):**

  **Setup:** Challenger runs (pk, sk) ← KEM.keygen.

  **Phase 1:** Adversary receives sk (the "semi-honest" party's
  compromised secret key). Adversary outputs an arbitrary public
  key pk' (possibly ≠ pk).

  **Challenge:** Challenger computes (ss, ct) ← KEM.encaps(pk').
  Adversary receives ct.

  **Phase 2:** Adversary outputs ct'.

  **Winning condition:** ct' ≠ ct ∧ KEM.decaps(sk, ct') = ss.

That is: the adversary, knowing sk, finds a *different* ciphertext
ct' that decapsulates (under the honest sk) to the same shared
secret ss that was encapsulated under the adversary-chosen pk'.

Security means: the probability of winning is negligible.

Formally:
  Adv^{SH-CR}_{KEM}(A) =
    Pr[ (pk,sk) ← keygen;
        pk' ← A(sk);
        (ss, ct) ← encaps(pk');
        ct' ← A(ct)
      : ct' ≠ ct ∧ decaps(sk, ct') = ss ]
-/
opaque KEM_SH_CR (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS) : Prop

/-- §4, Theorem 5 hypothesis: Kyber's internal hash functions (H, G,
XOF) behave as Random Oracles.

This is distinct from `KDF_RandomOracle` — it concerns the hash
functions *inside* the KEM construction (Kyber/ML-KEM), not the
protocol-level KDF. The paper proves that Kyber satisfies SH-CR
under this assumption. -/
opaque KEM_InternalHash_ROM (PK SK_kem CT SS : Type _)
    (kem : KEM PK SK_kem CT SS) : Prop

/-! ## Protocol security properties

Each property is defined relative to:
  - The protocol primitives (KEM, KDF, AEAD, Sig, DH group).
  - The adversary model (Dolev-Yao or computational AKE game).
  - A freshness condition (for computational properties).

### Secrecy (indistinguishability)

In the AKE game, the adversary receives either the real session
key or a random one (`Test` query) and must guess which. The
protocol is secure if no fresh adversary has non-negligible
advantage.

### Authentication (correspondence / matching sessions)

If an honest party completes a session believing it communicated
with a specific peer, then that peer must have participated in a
matching session with consistent transcript and key material.

### Agreement

Both parties agree on the same values for specific protocol
parameters (identities, SPK, OPK, PQSPK). Agreement is proved
as part of authentication — the matching session has the same
parameter values.
-/

/-- Message secrecy in the AKE security game.

The session key derived by PQXDH is indistinguishable from random
for any adversary that:
  - Controls the network (active MitM).
  - May corrupt long-term keys and reveal session keys.
  - Satisfies the freshness condition for the test session.

Parameterized by the group (for DH), the KEM (for PQ component),
and the KDF (which derives the session key).
This is the "real-or-random" indistinguishability game on the
output of `KDF.derive(DH1 ‖ DH2 ‖ DH3 ‖ DH4 ‖ ss)`. -/
opaque MessageSecrecy (G : Type _) [AddCommGroup G]
    (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS)
    (I K : Type _) (kdf : KDF I K)
    (fresh : Freshness) : Prop

/-- Peer authentication with identity and key agreement.

If Bob completes a PQXDH session believing he is talking to Alice,
then Alice initiated a matching session with Bob, and both agree on:
  - Identity keys: IKₐ, IKᵦ  (both parties know who they're talking to)
  - Signed prekey: SPKᵦ       (same medium-term key used)
  - One-time prekey: OPKᵦ     (same one-time key used, if present)

This subsumes "data agreement over the shared pre-key" (which the
paper lists as property (6) of Theorem 1).

This is a **correspondence assertion** in the ProVerif sense, or
an **authentication with agreement** property in the CryptoVerif
game.

**Caveat (Theorem 2):** In X25519, which has cofactor 8, agreement
on DH values holds only modulo the small subgroup of order 8. The
paper notes this explicitly: "modulo the subgroup elements of
X25519." -/
opaque PeerAuth (G : Type _) [AddCommGroup G]
    (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS)
    (I K : Type _) (kdf : KDF I K) : Prop

/-- Extended peer authentication: `PeerAuth` plus agreement over
the post-quantum signed prekey (PQSPK / KEM public key).

Standard `PeerAuth` (Theorem 2) does NOT guarantee PQSPK agreement.
A malicious server could substitute PQSPK without detection (the
re-encapsulation attack). This stronger property requires the
additional SH-CR assumption on the KEM (Theorem 6). -/
opaque PeerAuthPQ (G : Type _) [AddCommGroup G]
    (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS)
    (I K : Type _) (kdf : KDF I K) : Prop

/-- `PeerAuthPQ` implies `PeerAuth`: PQSPK agreement is strictly
stronger, adding one more agreed parameter. -/
theorem PeerAuthPQ_implies_PeerAuth
    (G : Type _) [AddCommGroup G]
    (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS)
    (I K : Type _) (kdf : KDF I K) :
    PeerAuthPQ G PK SK_kem CT SS kem I K kdf →
    PeerAuth G PK SK_kem CT SS kem I K kdf := by
  sorry

/-- Forward secrecy: even if all long-term identity keys (IKₐ, IKᵦ)
are compromised **after** a session completes, the session key
remains indistinguishable from random.

This holds because the session key depends on ephemeral keys (EKₐ)
and medium-term keys (SPKᵦ) that are deleted after use. The
adversary cannot recompute DH3 = DH(ekₐ, SPKᵦ) without the
ephemeral private key ekₐ, which no longer exists.

In the AKE game: `Corrupt` queries issued *after* the test session
completes do not violate freshness. -/
opaque ForwardSecrecy (G : Type _) [AddCommGroup G]
    (I K : Type _) (kdf : KDF I K) : Prop

/-- Resistance to Key Compromise Impersonation (KCI).

If Alice's long-term identity key ikₐ is compromised, an attacker
can impersonate Alice to others (since they have her signing key).
However, the attacker **cannot** impersonate *Bob to Alice* — Alice
can still authenticate Bob, because authenticating Bob requires
Bob's identity key ikᵦ (via DH2), which the attacker does not have.

Formally: compromise of IKₐ does not help the adversary forge a
session where Alice accepts Bob as the peer.

In the AKE game: a `Corrupt(Alice)` query before the test session
does not violate freshness (only `Corrupt(Alice) ∧ Corrupt(Bob)`
before completion violates freshness). -/
opaque KCI_Resistance (G : Type _) [AddCommGroup G] : Prop

/-- Session independence: the session key of one session is
independent of all other session keys.

Compromise of a session key SK_i (via `RevealSessionKey`) does not
help the adversary attack a different session SK_j, provided the
ephemeral keys are independently generated.

In the AKE game: the adversary may `RevealSessionKey` on any
session except the test session (and its partner), and still
cannot distinguish the test session's key from random. -/
opaque SessionIndependence (G : Type _) [AddCommGroup G]
    (I K : Type _) (kdf : KDF I K) : Prop

/-- Harvest-Now-Decrypt-Later (HNDL) resistance.

A *passive* quantum adversary who records all ciphertexts today
(including DH public keys and KEM ciphertexts) cannot recover
session keys in the future when a quantum computer becomes
available, provided the KEM remains secure (IND-CCA).

Formally: the adversary is given the power to compute discrete
logarithms (break DH) at some future time t_q. For any session
completed before t_q, if the KEM shared secret ss was part of
the KDF input, the session key remains indistinguishable from
random.

This is the core post-quantum guarantee of PQXDH over X3DH:
the KEM shared secret provides a "quantum-resistant backup" that
protects the session key even when all DH values are computable. -/
opaque HNDL_Resistance (G : Type _) [AddCommGroup G]
    (PK SK_kem CT SS : Type _) (kem : KEM PK SK_kem CT SS)
    (I K : Type _) (kdf : KDF I K) : Prop
