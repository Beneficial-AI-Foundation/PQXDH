/-
Main security theorems from:

  Bhargavan, Jacomme, Kiefer, Schmidt.
  "Formal verification of the PQXDH Post-Quantum key agreement
   protocol for end-to-end secure messaging."
  USENIX Security 2024.

Each theorem is stated at the top level with its cryptographic
hypotheses. Proofs are `sorry` — they correspond to computational
reductions machine-checked in CryptoVerif and symbolic analyses
machine-checked in ProVerif by the paper authors.

## Theorem overview

  **Theorem 1** (symbolic, ProVerif): PQXDH is secure in the
  Dolev-Yao model — peer authentication (including data agreement
  over the shared pre-key), forward secrecy, KCI resistance,
  session independence, and HNDL resistance.

  **Theorem 2** (classical computational, CryptoVerif): Under
  gapDH + ROM + IND-CPA/INT-CTXT + EUF-CMA, PQXDH provides
  message secrecy and peer authentication with identity/key
  agreement (modulo X25519 subgroup elements).

  **Theorem 3** (post-quantum computational, CryptoVerif): Under
  IND-CCA (KEM) + PRF (KDF) + IND-CPA/INT-CTXT (AEAD) + EUF-CMA
  (at time of exchange), the session key remains secret even if
  DH is broken later. **No DH assumption is required.**

  **Theorem 5** (§4): Kyber is SH-CR under ROM for its internal
  hash functions.

  **Theorem 6** (§4): Under the classical assumptions plus SH-CR,
  PQXDH additionally provides agreement over the PQSPK (KEM
  public key).
-/
import PQXDHLean.MainResult.SecurityDefs
import PQXDHLean.MainResult.PQXDH

variable {G : Type _} [AddCommGroup G]
variable {PK_kem SK_kem CT_kem SS : Type _}
variable {PK_sig SK_sig : Type _}
variable {M S_sig : Type _}
variable {SK_session PT CT_aead AD : Type _}

/-! ## Theorem 1 — Symbolic security (ProVerif)

**Model:** Dolev-Yao (symbolic). The adversary controls the network
(intercept, inject, replay, modify all messages) but cryptographic
primitives are **ideal black boxes** — encryption is perfect,
signatures are unforgeable, hashes are one-way, unless the adversary
possesses the relevant key.

**Verification tool:** ProVerif (automated symbolic protocol verifier).

**Properties verified:** correspondence assertions encoding
authentication, secrecy (as reachability), and agreement.

**Note:** This theorem has NO computational hardness hypotheses.
In the symbolic model, security follows from the protocol logic
alone, not from assumptions about specific primitives. The only
input is the Dolev-Yao adversary model.

This is the umbrella result implied by the detailed symbolic
Theorems 7, 8, 9 in Appendix A of the paper.
-/

/-- Theorem 1 (§3.1): In the Dolev-Yao model, PQXDH provides:
  (1) peer authentication (including data agreement over IKₐ, IKᵦ,
      SPKᵦ, OPKᵦ — the "shared pre-key" agreement),
  (2) forward secrecy,
  (3) resistance to key compromise impersonation (KCI),
  (4) session independence,
  (5) resistance to harvest-now-decrypt-later (HNDL) attacks
      in case of a DH breakdown.

The HNDL property specifically means: if the adversary gains the
ability to break DH (compute discrete logs) at time t_q, sessions
completed before t_q remain secure, because the KEM shared secret
(which the Dolev-Yao adversary cannot extract without the KEM
secret key) is part of the KDF input.

No computational assumptions are needed — the Dolev-Yao model
treats all primitives as ideal. -/
theorem PQXDH_symbolic_security
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (kdf : KDF ((G × G × G × G) × SS) SK_session)
    (_adversary : DolevYao) :
    PeerAuth G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf ∧
    ForwardSecrecy G ((G × G × G × G) × SS) SK_session kdf ∧
    KCI_Resistance G ∧
    SessionIndependence G ((G × G × G × G) × SS) SK_session kdf ∧
    HNDL_Resistance G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf := by
  sorry

/-! ## Theorem 2 — Classical computational security (CryptoVerif)

**Model:** Computational (game-based). The adversary is a
probabilistic polynomial-time (PPT) algorithm interacting with
an AKE game challenger via oracle queries: `NewSession`, `Send`,
`Corrupt`, `RevealSessionKey`, `Test`.

**Verification tool:** CryptoVerif (computational protocol verifier).

**Security game:** The adversary adaptively opens sessions, delivers
messages, corrupts long-term keys, and reveals session keys. It
then issues a `Test` query on a fresh session and must distinguish
the real session key from a random one.

**Assumptions (§2.5):**
  - 1.A: gapDH is hard on X25519
  - 2 (classical): KDF (HKDF-SHA-256) is a Random Oracle
  - 3: AEAD (AES-256-CBC + HMAC) is IND-CPA + INT-CTXT
  - 4: Signature (XEdDSA) is EUF-CMA

**Caveat (modulo subgroup elements):** X25519 is not a prime-order
group — it has a cofactor of 8. Agreement on DH values holds only
modulo the small subgroup. The paper notes this explicitly.
-/

/-- Theorem 2 (§3.2): If the gapDH problem is hard on the DH group
(with generator G₀), the KDF is a Random Oracle, the AEAD is
IND-CPA + INT-CTXT, and the signature scheme is EUF-CMA, then
PQXDH guarantees:
  (a) message secrecy — the session key is indistinguishable from
      random for any fresh adversary in the AKE game, and
  (b) peer authentication with agreement over identity keys (IKₐ, IKᵦ),
      the signed prekey (SPKᵦ), and the one-time prekey (OPKᵦ),
      modulo X25519 subgroup elements.

Note: this does NOT guarantee agreement over PQSPK (see Theorem 6). -/
theorem PQXDH_classical_security
    (G₀ : G)
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (kdf : KDF ((G × G × G × G) × SS) SK_session)
    (aead : AEAD SK_session PT CT_aead AD)
    (sig : Sig PK_sig SK_sig M S_sig)
    (fresh : Freshness)
    (h_gapdh : GapDH_Hard G G₀)
    (h_kdf_ro : KDF_RandomOracle ((G × G × G × G) × SS) SK_session kdf)
    (h_aead : AEAD_IND_CPA_INT_CTXT SK_session PT CT_aead AD aead)
    (h_sig : Sig_EUF_CMA PK_sig SK_sig M S_sig sig) :
    MessageSecrecy G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf fresh ∧
    PeerAuth G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf := by
  sorry

/-! ## Theorem 3 — Post-quantum computational security (CryptoVerif)

**Model:** Same computational AKE game as Theorem 2, but with a
**weaker assumption set** that does not include gapDH.

**Key insight:** This theorem makes **no assumption about DH**.
The DH group may be completely broken (e.g. by a quantum computer).
Security of the session key rests entirely on the KEM and KDF.

**Assumptions (§2.5):**
  - 1.B: KEM (Kyber-1024) is IND-CCA
  - 2 (PQ): KDF is a PRF (not ROM — CryptoVerif's PQ soundness
    does not capture the QROM)
  - 3: AEAD is IND-CPA + INT-CTXT
  - 4: Signature was EUF-CMA **at the time of the key exchange**
    (may be broken later by a quantum computer — the important
    thing is that it was secure when the session was established)

**Conclusion:** The session key remains secret even if DH is broken
in the future. This is precisely the HNDL resistance guarantee.

**Comparison with Theorem 2:**
  - Theorem 2 provides full classical security (authentication +
    secrecy) assuming DH is hard.
  - Theorem 3 provides post-quantum forward secrecy (session key
    secrecy) without any DH assumption.
  - Together: PQXDH is at least as secure as X3DH classically
    (Theorem 2), and additionally HNDL-resistant (Theorem 3).
-/

/-- Theorem 3 (§3.2): Under IND-CCA for the KEM, if the KDF is a
PRF, the AEAD is IND-CPA + INT-CTXT, and the signature scheme was
EUF-CMA at the time of the key exchange, then the session key
remains indistinguishable from random even if the DH problem is
broken in the future (e.g. by a quantum computer).

Note: no `GapDH_Hard` hypothesis appears — this is intentional.
The entire security rests on the KEM + KDF + AEAD + Sig (at time
of exchange).

The `HeldAtExchange` wrapper on `Sig_EUF_CMA` reflects the temporal
qualification: the signature scheme only needs to have been secure
*when the session was established*, not in perpetuity. A quantum
adversary may break it later without retroactively compromising
existing sessions. -/
theorem PQXDH_postquantum_security
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (kdf : KDF ((G × G × G × G) × SS) SK_session)
    (aead : AEAD SK_session PT CT_aead AD)
    (sig : Sig PK_sig SK_sig M S_sig)
    (fresh : Freshness)
    (h_kem_cca : KEM_IND_CCA PK_kem SK_kem CT_kem SS kem)
    (h_kdf_prf : KDF_PRF ((G × G × G × G) × SS) SK_session kdf)
    (h_aead : AEAD_IND_CPA_INT_CTXT SK_session PT CT_aead AD aead)
    (h_sig_at_exchange : HeldAtExchange
        (Sig_EUF_CMA PK_sig SK_sig M S_sig sig)) :
    HNDL_Resistance G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf := by
  sorry

/-! ## Theorem 5 — Kyber is SH-CR (§4)

**Context:** The paper discovered a KEM re-encapsulation attack
against PQXDH v1, where a malicious server replaces Bob's PQSPK
with a different key. To prove that PQXDH v2 resists this attack,
they introduced the SH-CR property (Definition 1) and proved that
Kyber satisfies it.

**Assumption:** The hash functions internal to Kyber (H, G, and XOF
in the NIST specification) behave as Random Oracles. This is a
standard assumption in Kyber's security analysis.

**Note:** The hypothesis is `KEM_InternalHash_ROM`, NOT `KEM_IND_CCA`.
SH-CR is a distinct property from IND-CCA. The paper proves it via
a separate reduction to the ROM on Kyber's hashes.
-/

/-- Theorem 5 (§4): Kyber-1024 (ML-KEM) satisfies Semi-Honest
Collision Resistance (SH-CR) under the Random Oracle Model for
its internal hash functions (H, G, XOF).

The reduction shows that any SH-CR adversary can be turned into
an adversary that finds collisions or preimages in the internal
hashes, which contradicts the ROM assumption. -/
theorem Kyber_SH_CR
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (h_hash_rom : KEM_InternalHash_ROM PK_kem SK_kem CT_kem SS kem) :
    KEM_SH_CR PK_kem SK_kem CT_kem SS kem := by
  sorry

/-! ## Theorem 6 — KEM public key agreement (§4)

**Context:** Theorem 2 establishes authentication with agreement over
IKₐ, IKᵦ, SPKᵦ, OPKᵦ. But it does NOT guarantee agreement over
PQSPK — the KEM public key. A malicious server could substitute
PQSPK without being detected (the re-encapsulation attack).

Theorem 6 closes this gap: under the classical assumptions PLUS
SH-CR for the KEM, both parties additionally agree on which PQSPK
was used. This gives the full `PeerAuthPQ` guarantee.

**Assumptions:** All of Theorem 2's assumptions, plus:
  - KEM is SH-CR (which, by Theorem 5, holds if Kyber's internal
    hashes are Random Oracles).
-/

/-- Theorem 6 (§4): Under the classical assumptions (gapDH, ROM KDF,
IND-CPA + INT-CTXT AEAD, EUF-CMA signature) plus Semi-Honest
Collision Resistance for the KEM, PQXDH provides extended peer
authentication with agreement over the PQSPK (KEM public key)
used in the exchange.

This strengthens Theorem 2's `PeerAuth` to `PeerAuthPQ`, adding
PQSPK agreement. -/
theorem PQXDH_KEM_pubkey_agreement
    (G₀ : G)
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (kdf : KDF ((G × G × G × G) × SS) SK_session)
    (aead : AEAD SK_session PT CT_aead AD)
    (sig : Sig PK_sig SK_sig M S_sig)
    (h_gapdh : GapDH_Hard G G₀)
    (h_kdf_ro : KDF_RandomOracle ((G × G × G × G) × SS) SK_session kdf)
    (h_aead : AEAD_IND_CPA_INT_CTXT SK_session PT CT_aead AD aead)
    (h_sig : Sig_EUF_CMA PK_sig SK_sig M S_sig sig)
    (h_shcr : KEM_SH_CR PK_kem SK_kem CT_kem SS kem) :
    PeerAuthPQ G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf := by
  sorry
