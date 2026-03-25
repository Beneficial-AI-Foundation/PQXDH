/-
PQXDH protocol definition and main security theorems.

Extends X3DH with a post-quantum KEM encapsulation. The KEM shared
secret is concatenated into the KDF input alongside the DH shared
secrets, providing resistance to harvest-now-decrypt-later attacks.

Reference: Bhargavan et al. §2.1–§2.3, Figure 1.
  USENIX Security 2024.

## Protocol overview (Figure 1)

Bob publishes a prekey bundle to the server:
  - IKᵦ     = [ikᵦ]·G    (long-term identity key)
  - SPKᵦ    = [spkᵦ]·G   (signed prekey, rotated periodically)
  - Sig_ᵦ               (signature over SPKᵦ using ikᵦ — authenticates SPK)
  - OPKᵦ    = [opkᵦ]·G   (one-time prekey, consumed after single use)
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
import PQXDHLean.DH
import PQXDHLean.KDF
import PQXDHLean.AEAD
import PQXDHLean.KEM
import PQXDHLean.SecurityDefs

variable {G : Type _} [AddCommGroup G]

/-! ## PQXDH key bundle

Bob publishes the classical X3DH keys plus a PQ-KEM public key (PQSPK),
each signed prekey accompanied by a signature under Bob's identity key.
-/

/-- §2.3, p. 472 and Figure 1, p. 471: Bob's prekey bundle including the
post-quantum KEM public key and signatures authenticating the signed prekeys.
"In the initial message to Alex, Blake includes PQSPKᵦᵖᵏ and
sign(PQSPKᵦᵖᵏ, IKᵦˢᵏ)." (§2.3, item 2, p. 472) -/
structure PQXDHBundle (G PK_kem S_sig : Type _) [AddCommGroup G] where
  IKᵦ : G            -- long-term identity public key
  SPKᵦ : G           -- signed prekey (medium-term)
  sig_spk : S_sig     -- signature over SPKᵦ under IKᵦ
  OPKᵦ : G           -- one-time prekey
  PQSPK : PK_kem     -- post-quantum signed prekey (KEM public key)
  sig_pqspk : S_sig   -- signature over PQSPK under IKᵦ

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

/-- §2.3, p. 472 and Figure 1, p. 471: Alice's view of the PQXDH key exchange.
Four DH values plus the KEM encapsulation output (ct, ss).
"When computing the session secret, Alex also computes CT, SS ← KEM.encaps(PQSPKᵦᵖᵏ)
and concatenates SS to the X3DH Key Derivation Function input." (§2.3, item 3) -/
noncomputable def PQXDH_Alice
    {PK_kem SK_kem CT SS S_sig : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (ikₐ ekₐ : ℕ) (bundle : PQXDHBundle G PK_kem S_sig) :
    (G × G × G × G) × (CT × SS) :=
  let dh := (DH ikₐ bundle.SPKᵦ,
             DH ekₐ bundle.IKᵦ,
             DH ekₐ bundle.SPKᵦ,
             DH ekₐ bundle.OPKᵦ)
  let kem_out := kem.encaps bundle.PQSPK
  (dh, kem_out)

/-- §2.3, p. 472 and Figure 1, p. 471: Bob's view of the PQXDH key exchange.
Four DH values plus the KEM decapsulation of ct.
"Blake uses their private key to compute SS = KEM.decaps(CT, PQSPKᵦˢᵏ)
and also concatenates it to the X3DH Key Derivation Function input." (§2.3, item 5) -/
noncomputable def PQXDH_Bob
    {PK_kem SK_kem CT SS : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (ikᵦ spkᵦ opkᵦ : ℕ) (sk_kem : SK_kem)
    (IKₐ EKₐ : G) (ct : CT) :
    (G × G × G × G) × SS :=
  let dh := (DH spkᵦ IKₐ,
             DH ikᵦ EKₐ,
             DH spkᵦ EKₐ,
             DH opkᵦ EKₐ)
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
SK_B = kdf((SPKᵦᵖᵏ)^{IKₐˢᵏ} ‖ (IKᵦᵖᵏ)^{EKₐˢᵏ} ‖ (SPKᵦᵖᵏ)^{EKₐˢᵏ} ‖ SS). -/
noncomputable def PQXDH_SK_Alice
    {PK_kem SK_kem CT SS S_sig : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (kdf : KDF ((G × G × G × G) × SS) SK)
    (ikₐ ekₐ : ℕ) (bundle : PQXDHBundle G PK_kem S_sig) : SK :=
  let (dh, (_, ss)) := PQXDH_Alice kem ikₐ ekₐ bundle
  kdf.derive (dh, ss)

/-- Figure 1, p. 471: Bob derives the PQXDH session key
SKₐ = kdf((IKₐᵖᵏ)^{SPKᵦˢᵏ} ‖ (EKₐᵖᵏ)^{IKᵦˢᵏ} ‖ (EKₐᵖᵏ)^{SPKᵦˢᵏ} ‖ SS). -/
noncomputable def PQXDH_SK_Bob
    {PK_kem SK_kem CT SS : Type _}
    (kem : KEM PK_kem SK_kem CT SS)
    (kdf : KDF ((G × G × G × G) × SS) SK)
    (ikᵦ spkᵦ opkᵦ : ℕ) (sk_kem : SK_kem)
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
    (ikₐ ekₐ ikᵦ spkᵦ opkᵦ : ℕ)
    (sk_kem : SK_kem) (pk_kem : PK_kem)
    (s1 s2 : S_sig)
    {IKₐ EKₐ IKᵦ SPKᵦ OPKᵦ : G}
    (hIKₐ : IKₐ = DH ikₐ G₀)
    (hEKₐ : EKₐ = DH ekₐ G₀)
    (hIKᵦ : IKᵦ = DH ikᵦ G₀)
    (hSPKᵦ : SPKᵦ = DH spkᵦ G₀)
    (hOPKᵦ : OPKᵦ = DH opkᵦ G₀)
    (bundle : PQXDHBundle G PK_kem S_sig)
    (hBundle : bundle = ⟨IKᵦ, SPKᵦ, s1, OPKᵦ, pk_kem, s2⟩)
    (ct : CT) (ss : SS)
    (hEncaps : kem.encaps pk_kem = (ct, ss))
    (hDecaps : kem.decaps sk_kem ct = ss) :
    PQXDH_SK_Alice kem kdf ikₐ ekₐ bundle =
    PQXDH_SK_Bob kem kdf ikᵦ spkᵦ opkᵦ sk_kem IKₐ EKₐ ct := by
  subst hIKₐ; subst hEKₐ; subst hIKᵦ; subst hSPKᵦ; subst hOPKᵦ; subst hBundle
  simp only [PQXDH_SK_Alice, PQXDH_SK_Bob, PQXDH_Alice, PQXDH_Bob,
             DH_comm, hEncaps, hDecaps]

/-! ## Theorem 1 — Symbolic security (ProVerif)

In the Dolev-Yao model, PQXDH provides peer authentication,
forward secrecy, KCI resistance, session independence, and
HNDL resistance. No computational hardness hypotheses are needed. -/

variable {PK_kem SK_kem CT_kem SS : Type _}
variable {PK_sig SK_sig : Type _}
variable {M S_sig : Type _}
variable {SK_session PT CT_aead AD : Type _}

/-- Theorem 1, §5.2 p. 479: "PQXDH in the symbolic model provides peer-
authentication, forward secrecy, resistance to key compromise impersonation,
session independence and resistance to 'harvest now decrypt later' attacks
in case of a DH break down. In addition, it also provides data agreement
over the shared pre-key used."
No computational hardness hypotheses needed. Verified by ProVerif (Theorems 7–9, Appendix A). -/
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

Under gapDH + ROM + IND-CPA/INT-CTXT + EUF-CMA, PQXDH provides
message secrecy and peer authentication with identity/key agreement
(modulo X25519 subgroup elements). -/

/-- Theorem 2, §5.2 p. 479: "If X25519 satisfies the gapDH assumption, the KDF
is a Random Oracle, if the AEAD is IND-CPA+INT-CTXT and if the signature scheme
is EUF-CMA, then PQXDH guarantees both the secrecy of the sent message, as-well-as
peer-authentication with agreement over identities, OPK and SPK used, modulo the
subgroup elements of X25519." Verified by CryptoVerif. -/
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

Under IND-CCA (KEM) + PRF (KDF) + IND-CPA/INT-CTXT (AEAD) +
EUF-CMA (at time of exchange), the session key remains secret
even if DH is broken later. No DH assumption is required. -/

/-- Theorem 3, §5.2 p. 479: "Under IND-CCA for the KEM, if the KDF is a PRF and
the final AEAD is IND-CPA+INT-CTXT, as long as the signature scheme was unforgeable
when some key exchange was completed, secrecy of the derived key still holds in the
future." No DH assumption required. Verified by CryptoVerif. -/
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

Kyber-1024 satisfies Semi-Honest Collision Resistance under the
Random Oracle Model for its internal hash functions. -/

/-- Theorem 5, §5.3.2 p. 480: "If the hash functions used in the Kyber design
are modeled as Random Oracles, Kyber is SH-CR." -/
theorem Kyber_SH_CR
    (kem : KEM PK_kem SK_kem CT_kem SS)
    (h_hash_rom : KEM_InternalHash_ROM PK_kem SK_kem CT_kem SS kem) :
    KEM_SH_CR PK_kem SK_kem CT_kem SS kem := by
  sorry

/-! ## Theorem 6 — KEM public key agreement (§4)

Under the classical assumptions plus SH-CR for the KEM, PQXDH
provides extended peer authentication with agreement over PQSPK. -/

/-- Theorem 6, §5.3.2 p. 480: "Under similar hypothesis as Theorem 2, PQXDH
also guarantees the agreement over the PQSPK used provided the KEM is SH-CR."
Strengthens Theorem 2's `PeerAuth` to `PeerAuthPQ`. -/
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
