/-
PQXDH protocol definition and main security theorems.

Extends X3DH with a post-quantum KEM encapsulation. The KEM shared
secret is concatenated into the KDF input alongside the DH shared
secrets, providing resistance to harvest-now-decrypt-later attacks.

All DH proofs rely on the `Module F G` API from `DH.lean`, which covers
every algebraic property needed here (`smul_smul`, `mul_comm`, etc.).

Reference: Bhargavan et al. §2.1–§2.3, Figure 1.
  USENIX Security 2024.

## Protocol overview (Figure 1)

Bob publishes a prekey bundle to the server:
  - IKᵦ     = ikᵦ • G₀   (long-term identity key)
  - SPKᵦ    = spkᵦ • G₀  (signed prekey, rotated periodically)
  - Sig_ᵦ               (signature over SPKᵦ using ikᵦ — authenticates SPK)
  - OPKᵦ    = opkᵦ • G₀  (one-time prekey, consumed after single use)
  - PQSPK_ᵦ             (KEM public key, post-quantum signed prekey)
  - PQSig_ᵦ             (signature over PQSPK_ᵦ using ikᵦ)

Alice fetches the bundle, verifies both signatures, then computes:
  1. DH1 = DH(ikₐ,  SPKᵦ)     — mutual authentication (Alice's side)
  2. DH2 = DH(ekₐ,  IKᵦ)      — mutual authentication (Bob's side)
  3. DH3 = DH(ekₐ,  SPKᵦ)     — forward secrecy
  4. DH4 = DH(ekₐ,  OPKᵦ)     — replay protection
  5. (ct, ss) = KEM.encaps(PQSPK_ᵦ) — post-quantum protection

  SK = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4 ‖ ss)
  AD = Encode(IKₐ) ‖ Encode(IKᵦ)

Alice sends to Bob: (IKₐ, EKₐ, ct, AEAD.encrypt(SK, msg, AD))

Bob verifies, computes the same DH values (by commutativity),
decapsulates ct to recover ss, derives SK, and decrypts.

## Main security theorems

Each theorem is stated at the top level with its cryptographic
hypotheses. Proofs are `sorry` — they correspond to computational
reductions machine-checked in CryptoVerif and symbolic analyses
machine-checked in ProVerif by the paper authors.
-/
import PQXDHLean.X3DH.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD
import PQXDHLean.KEM
import PQXDHLean.SecurityDefs

variable {F : Type _} [Field F]
variable {G : Type _} [AddCommGroup G] [Module F G]

/-! ## PQXDH key bundle

Bob publishes the classical X3DH keys plus a PQ-KEM public key (PQSPK),
each signed prekey accompanied by a signature under Bob's identity key.
-/

/-- §2.3, p. 472 and Figure 1, p. 471: Bob's prekey bundle including the
post-quantum KEM public key and signatures authenticating the signed prekeys.
"In the initial message to Alex, Blake includes PQSPKᵦᵖᵏ and
sign(PQSPKᵦᵖᵏ, IKᵦˢᵏ)." (§2.3, item 2, p. 472) -/
structure PQXDHBundle (G PK_kem S_sig : Type _) [AddCommGroup G] where
  IKᵦ : G             -- long-term identity public key
  SPKᵦ : G            -- signed prekey (medium-term)
  sig_spk : S_sig      -- signature over SPKᵦ under IKᵦ
  OPKᵦ : Option G     -- one-time prekey (optional; absent when the server has no remaining OPKs)
  PQSPK : PK_kem      -- post-quantum signed prekey (KEM public key)
  sig_pqspk : S_sig    -- signature over PQSPK under IKᵦ

/-! ## Signature verification

Alice must verify the signatures on SPKᵦ and PQSPK before
using the bundle. This prevents a malicious server from
substituting Bob's signed prekeys. -/

/-- Figure 1, p. 471 "Verify signatures": Alice verifies Bob's bundle
signatures before proceeding. Returns `true` iff both the SPK signature
and the PQSPK signature are valid under Bob's identity public key. -/
def PQXDHBundle.verify_signatures
    {PK_sig SK_sig M S_sig PK_kem : Type _}
    (bundle : PQXDHBundle G PK_kem S_sig)
    (sig_scheme : Sig PK_sig SK_sig M S_sig)
    (IKᵦ_sig : PK_sig)
    (encode_spk : G → M) (encode_pqspk : PK_kem → M) : Bool :=
  sig_scheme.verify IKᵦ_sig (encode_spk bundle.SPKᵦ) bundle.sig_spk &&
  sig_scheme.verify IKᵦ_sig (encode_pqspk bundle.PQSPK) bundle.sig_pqspk

/-! ## PQXDH shared secret computation

Alice computes the four classical DH values plus the KEM shared secret.
The five values are concatenated and fed to the KDF.
-/

/-- §2.3, p. 472 and Figure 4, p. 484: Alice's view of the PQXDH key exchange.
Four DH values plus the KEM encapsulation output (ct, ss).
"When computing the session secret, Alex also computes CT, SS ← KEM.encaps(PQSPKᵦᵖᵏ)
and concatenates SS to the X3DH Key Derivation Function input." (§2.3, item 3)
When no OPK is present, DH4 defaults to 0 (the group identity). -/
def PQXDH_Alice
    {PK_kem SK_kem CT SS S_sig : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (ikₐ ekₐ : F) (bundle : PQXDHBundle G PK_kem S_sig) :
    (G × G × G × G) × (CT × SS) :=
  let dh := (DH ikₐ bundle.SPKᵦ,
             DH ekₐ bundle.IKᵦ,
             DH ekₐ bundle.SPKᵦ,
             DH ekₐ (bundle.OPKᵦ.getD 0))
  let kem_out := kem.encaps bundle.PQSPK
  (dh, kem_out)

/-- §2.3, p. 472 and Figure 4, p. 484: Bob's view of the PQXDH key exchange.
Four DH values plus the KEM decapsulation of ct.
"Blake uses their private key to compute SS = KEM.decaps(CT, PQSPKᵦˢᵏ)
and also concatenates it to the X3DH Key Derivation Function input." (§2.3, item 5)
When no OPK was used, `opkᵦ` is `none` and DH4 defaults to 0. -/
def PQXDH_Bob
    {PK_kem SK_kem CT SS : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (ikᵦ spkᵦ : F) (opkᵦ : Option F) (sk_kem : SK_kem)
    (IKₐ EKₐ : G) (ct : CT) :
    (G × G × G × G) × SS :=
  let dh := (DH spkᵦ IKₐ,
             DH ikᵦ EKₐ,
             DH spkᵦ EKₐ,
             DH (opkᵦ.getD 0) EKₐ)
  let ss := kem.decaps sk_kem ct
  (dh, ss)

/-! ## PQXDH session key derivation

The session key is derived from the concatenation of all DH outputs
and the KEM shared secret:

  SK = KDF(DH1 ‖ DH2 ‖ DH3 ‖ DH4 ‖ ss)

where ss is the KEM shared secret. The KDF input type is
`(G × G × G × G) × SS` — four DH group elements plus the KEM
shared secret.
-/

variable {SK : Type _}

/-- Figure 1, p. 471: Alice derives the PQXDH session key
SK_B = kdf(ikₐ • SPKᵦ ‖ ekₐ • IKᵦ ‖ ekₐ • SPKᵦ ‖ SS). -/
def PQXDH_SK_Alice
    {PK_kem SK_kem CT SS S_sig : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (kdf : KDF ((G × G × G × G) × SS) SK)
    (ikₐ ekₐ : F) (bundle : PQXDHBundle G PK_kem S_sig) : SK :=
  let (dh, (_, ss)) := PQXDH_Alice kem ikₐ ekₐ bundle
  kdf.derive (dh, ss)

/-- Figure 4, p. 484: Bob derives the PQXDH session key
SKₐ = kdf(spkᵦ • IKₐ ‖ ikᵦ • EKₐ ‖ spkᵦ • EKₐ ‖ SS). -/
def PQXDH_SK_Bob
    {PK_kem SK_kem CT SS : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (kdf : KDF ((G × G × G × G) × SS) SK)
    (ikᵦ spkᵦ : F) (opkᵦ : Option F) (sk_kem : SK_kem)
    (IKₐ EKₐ : G) (ct : CT) : SK :=
  let (dh, ss) := PQXDH_Bob kem ikᵦ spkᵦ opkᵦ sk_kem IKₐ EKₐ ct
  kdf.derive (dh, ss)

/-! ## PQXDH correctness (functional, not security)

Under honest key generation from the same generator, correct
KEM encapsulation/decapsulation, and verified signatures, Alice
and Bob derive the same session key. This extends `X3DH_agree`
with the KEM component. -/

/-- §2.1, p. 470 and Figure 1, p. 471: PQXDH functional correctness.
Under honest key generation and correct KEM encaps/decaps,
Alice and Bob derive the same session key (SKₐ = SK_B).
Extends `X3DH_agree` with the KEM component. -/
theorem PQXDH_agree
    {PK_kem SK_kem CT SS S_sig : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (kdf : KDF ((G × G × G × G) × SS) SK)
    (G₀ : G)
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : F)
    (sk_kem : SK_kem) (pk_kem : PK_kem)
    (s1 s2 : S_sig)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀)
    (bundle : PQXDHBundle G PK_kem S_sig)
    (hBundle : bundle = ⟨IKᵦ, SPKᵦ, s1, some OPKᵦ, pk_kem, s2⟩)
    (ct : CT) (ss : SS)
    (hEncaps : kem.encaps pk_kem = (ct, ss))
    (hDecaps : kem.decaps sk_kem ct = ss) :
    PQXDH_SK_Alice kem kdf ikₐ ekₐ bundle =
    PQXDH_SK_Bob kem kdf ikᵦ spkᵦ (some opkᵦ) sk_kem IKₐ EKₐ ct := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ; subst hOPKᵦ; subst hBundle
  simp only [PQXDH_SK_Alice, PQXDH_SK_Bob, PQXDH_Alice, PQXDH_Bob,
             DH, smul_smul, mul_comm, hEncaps, hDecaps, Option.getD_some]

/-! ## Security theorems

Theorem overview:
  - **Theorem 1** (symbolic, ProVerif): peer authentication, forward secrecy,
    KCI resistance, session independence, HNDL resistance.
  - **Theorem 2** (classical computational, CryptoVerif): message secrecy +
    peer authentication under gapDH + ROM + IND-CPA/INT-CTXT + EUF-CMA.
  - **Theorem 3** (post-quantum computational, CryptoVerif): session key
    secrecy under IND-CCA (KEM) + PRF + IND-CPA/INT-CTXT + EUF-CMA (at
    time of exchange). **No DH assumption.**
  - **Theorem 5** (§4): Kyber is SH-CR under ROM for internal hashes.
  - **Theorem 6** (§4): classical assumptions + SH-CR → PQSPK agreement.

Each proof is `sorry` — they correspond to computational reductions
machine-checked in CryptoVerif and symbolic analyses machine-checked
in ProVerif by the paper authors.
-/

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

**Note:** This theorem has NO computational hardness hypotheses.
In the symbolic model, security follows from the protocol logic
alone, not from assumptions about specific primitives.

This is the umbrella result implied by the detailed symbolic
Theorems 7, 8, 9 in Appendix A of the paper. -/

/-- Theorem 1 (§3.1): In the Dolev-Yao model, PQXDH provides:
  (1) extended peer authentication (`PeerAuthPQ`) — agreement over IKₐ,
      IKᵦ, SPKᵦ, OPKᵦ, **and** PQSPK (the KEM public key). In the
      symbolic model the adversary cannot break signatures, so PQSPK
      agreement follows directly from signature verification (Theorem 8
      of Appendix A). This is strictly stronger than the classical
      Theorem 2, which only gives `PeerAuth` without PQSPK agreement
      and requires the additional SH-CR assumption to obtain it
      (Theorem 6).
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
    PeerAuthPQ G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf ∧
    ForwardSecrecy G ((G × G × G × G) × SS) SK_session kdf ∧
    KCI_Resistance G ∧
    SessionIndependence G ((G × G × G × G) × SS) SK_session kdf ∧
    HNDL_Resistance G PK_kem SK_kem CT_kem SS kem
        ((G × G × G × G) × SS) SK_session kdf := by
  sorry

/-! ## Theorem 2 — Classical computational security (CryptoVerif)

**Model:** Computational (game-based). The adversary is a PPT algorithm
interacting with an AKE game challenger via oracle queries: `NewSession`,
`Send`, `Corrupt`, `RevealSessionKey`, `Test`.

**Assumptions (§2.5):**
  - 1.A: gapDH is hard on X25519
  - 2 (classical): KDF (HKDF-SHA-256) is a Random Oracle
  - 3: AEAD (AES-256-CBC + HMAC) is IND-CPA + INT-CTXT
  - 4: Signature (XEdDSA) is EUF-CMA

**Caveat (modulo subgroup elements):** X25519 is not a prime-order
group — it has a cofactor of 8. Agreement on DH values holds only
modulo the small subgroup. The paper notes this explicitly. -/

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

**Key insight:** This theorem makes **no assumption about DH**.
The DH group may be completely broken (e.g. by a quantum computer).
Security of the session key rests entirely on the KEM and KDF.

**Assumptions (§2.5):**
  - 1.B: KEM (Kyber-1024) is IND-CCA
  - 2 (PQ): KDF is a PRF (not ROM — CryptoVerif's PQ soundness
    does not capture the QROM)
  - 3: AEAD is IND-CPA + INT-CTXT
  - 4: Signature was EUF-CMA **at the time of the key exchange**

**Comparison with Theorem 2:**
  - Theorem 2 provides full classical security (authentication +
    secrecy) assuming DH is hard.
  - Theorem 3 provides post-quantum forward secrecy (session key
    secrecy) without any DH assumption.
  - Together: PQXDH is at least as secure as X3DH classically
    (Theorem 2), and additionally HNDL-resistant (Theorem 3).

**Why PRF instead of ROM/QROM (§3.5, p. 475):**
  The classical Theorem 2 models the KDF (HKDF-SHA-256) as a
  Random Oracle (ROM). The natural quantum analogue would use the
  Quantum Random Oracle Model (QROM), where the adversary queries
  the oracle in superposition. However, CryptoVerif's post-quantum
  soundness result does not capture the QROM, so the paper falls
  back to the PRF assumption.

  This is not merely a tool limitation — PRF is a theoretically
  legitimate and arguably preferable choice:
  - ROM/QROM assumes the KDF is an *ideal* random function
    (information-theoretic), which is a strong assumption.
  - PRF assumes only *computational* indistinguishability from
    random when keyed — a weaker, standard-model assumption.
  - Standard-model proofs (PRF) are considered stronger than
    ROM proofs, since there exist schemes provably secure in the
    ROM that are insecure for any concrete hash instantiation
    (Canetti–Goldreich–Halevi 1998).

  The cost of PRF vs. ROM is a potentially looser reduction bound.
  A QROM-based proof of Theorem 2 remains future work. -/

/-- Theorem 3 (§3.2): Under IND-CCA for the KEM, if the KDF is a
PRF, the AEAD is IND-CPA + INT-CTXT, and the signature scheme was
EUF-CMA at the time of the key exchange, then the session key
remains indistinguishable from random even if the DH problem is
broken in the future (e.g. by a quantum computer).

Note: no `GapDH_Hard` hypothesis appears — this is intentional.

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
SH-CR is a distinct property from IND-CCA. -/

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
    hashes are Random Oracles). -/

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
