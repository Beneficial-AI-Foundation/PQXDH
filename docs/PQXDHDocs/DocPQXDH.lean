import VersoManual
import VersoBlueprint
import PQXDHLean.PQXDH

open Verso.Genre Manual
open Informal


#doc (Manual) "The PQXDH Protocol" =>
%%%
tag := "pqxdh"
%%%

:::group "pqxdh_core"
PQXDH protocol definitions and roadmap from X3DH to full post-quantum security.
:::

The PQXDH (Post-Quantum Extended Diffie-Hellman) protocol extends X3DH by
adding a post-quantum KEM layer. The KEM shared secret is appended to the KDF
input alongside the four classical DH values, so the session key depends on
both classical and post-quantum contributions. A quantum adversary who can
break DH cannot recover the session key as long as the KEM remains secure —
providing resistance to harvest-now-decrypt-later attacks.

The protocol is analysed against both a symbolic adversary (ProVerif, Dolev-Yao
model) and a computational adversary (CryptoVerif, game-based model). The two
analyses give complementary guarantees (§3.6): the symbolic analysis covers
more compromise scenarios; the computational analysis provides quantitative
security bounds.

# Protocol bundle

:::definition "pqxdh_bundle" (lean := "PQXDHBundle") (parent := "pqxdh_core")
Bob's prekey bundle: the collection of public values Alice fetches from the
server before initiating a session. Contains the long-term identity key IKᵦ,
the medium-term signed prekey SPKᵦ and its signature, the optional one-time
prekey OPKᵦ (absent when the server has exhausted its supply), the
post-quantum signed prekey PQSPK (a KEM public key), and its signature.
Alice must verify both signatures before using any key material (Figure 4).
:::

:::definition "pqxdh_verify_signatures" (lean := "PQXDHBundle.verify_signatures") (parent := "pqxdh_core")
Alice verifies the two bundle signatures before using any key material. Both
the SPK and the PQSPK must be authenticated under Bob's identity public key.
The encoding functions `encode_spk` and `encode_pqspk` are passed as separate
parameters to enforce domain separation between EC and KEM public keys — the
fix for PQXDH v1 vulnerability F3 (§5.1). Returns `true` iff both
`sign(encode_spk SPKᵦ, IKᵦˢᵏ)` and `sign(encode_pqspk PQSPK, IKᵦˢᵏ)` verify
(Figure 4).
:::

# Shared secret computation

:::definition "pqxdh_alice" (lean := "PQXDH_Alice") (parent := "pqxdh_core")
Alice's contribution to the shared secret (Figure 4). Computes four DH values:

- DH1 = ikₐ • SPKᵦ — mutual authentication (Alice's identity key)
- DH2 = ekₐ • IKᵦ — mutual authentication (Bob's identity key)
- DH3 = ekₐ • SPKᵦ — forward secrecy
- DH4 = ekₐ • OPKᵦ — replay protection (0 when OPK is absent)

and encapsulates under the post-quantum signed prekey to obtain `(ct, ss)`.
:::

:::definition "pqxdh_bob" (lean := "PQXDH_Bob") (parent := "pqxdh_core")
Bob's contribution to the shared secret (Figure 4). Computes the same four DH
values by commutativity, and decapsulates Alice's ciphertext to recover `ss`.
`opkᵦ` is `none` when Alice did not use a one-time prekey.
:::

# Session key derivation

:::definition "pqxdh_sk_alice" (lean := "PQXDH_SK_Alice") (parent := "pqxdh_core")
Alice's PQXDH session key: {uses "kdf_spec"}[] applied to
`(DH1 ‖ DH2 ‖ DH3 ‖ DH4, ss)` where `ss` is the KEM shared secret.
:::

:::definition "pqxdh_sk_bob" (lean := "PQXDH_SK_Bob") (parent := "pqxdh_core")
Bob's PQXDH session key: {uses "kdf_spec"}[] applied to the same combined
transcript. Equals Alice's session key when keys are honestly generated and
the KEM round-trip is correct (see {uses "pqxdh_agree"}[]).
:::

# Agreement

:::theorem "pqxdh_agree" (lean := "PQXDH_agree") (parent := "pqxdh_core") (tags := "pqxdh, agreement") (effort := "medium") (priority := "high")
PQXDH functional correctness: Alice and Bob derive the same session key when
all EC key pairs are honestly generated from the same generator and the KEM
encapsulation and decapsulation are consistent (`hEncaps` and `hDecaps`). The
one-time prekey is taken as present (`some OPKᵦ`). The proof follows by DH
commutativity (`smul_smul`, `mul_comm`) together with unfolding the KEM
round-trip — it does not use {uses "kem_spec"}[]'s `correctness` field, whose
premises are already supplied as explicit hypotheses.
:::

# Security properties

:::theorem "pqxdh_symbolic_security" (lean := "PQXDH_symbolic_security") (parent := "pqxdh_core") (tags := "pqxdh, security, symbolic") (effort := "large") (priority := "high")
Symbolic security of PQXDH (Theorem 1, §3.1; detailed in Appendix A Theorems
7–9 proved by ProVerif). Under the Dolev-Yao adversary model — active
network control, adaptive key corruption, ideal cryptographic primitives — the
protocol satisfies all five security properties:

1. **Extended peer authentication** ({uses "peer_auth_pq"}[]) — agreement over
   IKₐ, IKᵦ, SPKᵦ, OPKᵦ, and PQSPK. The symbolic model gives PQSPK agreement
   for free: the adversary cannot forge signatures, so authenticated PQSPK
   delivery is guaranteed by Theorem 8 (Appendix A). This is stronger than the
   classical {uses "pqxdh_classical_security"}[], which reaches only
   {uses "peer_auth"}[] and requires the additional SH-CR assumption to recover
   PQSPK agreement via {uses "pqxdh_kem_pubkey_agreement"}[] (Theorem 6).
2. **Forward secrecy** — long-term key compromise after session completion does
   not reveal the session key.
3. **KCI resistance** — compromise of Alice's identity key does not allow
   impersonating Bob to Alice.
4. **Session independence** — revealing one session key does not compromise
   others.
5. **HNDL resistance** — a passive adversary who records ciphertexts today and
   later acquires the ability to compute discrete logarithms cannot decrypt
   past sessions, as long as the KEM shared secret remains protected.

No computational hardness assumptions are required; the Dolev-Yao model treats
all primitives as ideal.
:::

:::theorem "pqxdh_classical_security" (lean := "PQXDH_classical_security") (parent := "pqxdh_core") (tags := "pqxdh, security, classical") (effort := "large") (priority := "high")
Classical computational security of PQXDH (Theorem 2, §3.2; proved by
CryptoVerif). Under the assumptions that GapDH is hard on the DH group, the
KDF is a Random Oracle, the AEAD is IND-CPA + INT-CTXT, and the signature
scheme is EUF-CMA, the protocol achieves:

- **Message secrecy** ({uses "message_secrecy"}[]) — the session key is
  indistinguishable from random for any fresh AKE adversary.
- **Peer authentication** ({uses "peer_auth"}[]) — agreement over IKₐ, IKᵦ,
  SPKᵦ, and OPKᵦ, modulo X25519 subgroup elements (cofactor 8).

Note: this does **not** guarantee agreement over PQSPK; a malicious server
could substitute the KEM public key without detection under these assumptions
alone. PQSPK agreement requires the additional SH-CR assumption on the KEM
(see {uses "pqxdh_kem_pubkey_agreement"}[]).
:::

:::theorem "pqxdh_postquantum_security" (lean := "PQXDH_postquantum_security") (parent := "pqxdh_core") (tags := "pqxdh, security, postquantum") (effort := "large") (priority := "high")
Post-quantum forward secrecy of PQXDH (Theorem 3, §3.2; proved by CryptoVerif).
Under KEM IND-CCA, KDF PRF, AEAD IND-CPA + INT-CTXT, and EUF-CMA for the
signature scheme **at the time of the key exchange**, the session key is
{uses "hndl_resistance"}[] — indistinguishable from random even if DH is
completely broken by a future quantum computer.

Crucially, **no GapDH assumption appears** — the DH group may be fully
broken. Security rests entirely on the KEM and KDF. The `HeldAtExchange`
wrapper on the signature assumption reflects that the adversary may later
forge signatures without retroactively compromising established sessions.

The KDF is modelled as a PRF rather than a Random Oracle (as in Theorem 2)
because CryptoVerif's post-quantum soundness result does not capture the QROM
(§3.5, p. 475).
:::

:::theorem "kyber_sh_cr" (lean := "Kyber_SH_CR") (parent := "pqxdh_core") (tags := "pqxdh, kem, sh-cr") (effort := "medium") (priority := "medium")
Kyber-1024 (ML-KEM) satisfies Semi-Honest Collision Resistance
({uses "kem_sh_cr"}[], Definition 1, §5.3.1) under the assumption that
Kyber's internal hash functions H, G, and XOF behave as Random Oracles
(Theorem 5, §5.3.2). This is a distinct property from IND-CCA: SH-CR
ensures that a compromised secret key cannot be used to find a colliding
ciphertext under a different public key. It is the critical assumption
required by {uses "pqxdh_kem_pubkey_agreement"}[] to close the
re-encapsulation attack.
:::

:::theorem "pqxdh_kem_pubkey_agreement" (lean := "PQXDH_KEM_pubkey_agreement") (parent := "pqxdh_core") (tags := "pqxdh, kem, agreement") (effort := "small") (priority := "medium")
Extended peer authentication with PQSPK agreement (Theorem 6, §5.3.2). Under
the same classical assumptions as {uses "pqxdh_classical_security"}[] plus
{uses "kem_sh_cr"}[] for the KEM, PQXDH additionally guarantees agreement over
the post-quantum signed prekey PQSPK ({uses "peer_auth_pq"}[]).

This closes the gap left by Theorem 2: without SH-CR, a malicious server can
mount a re-encapsulation attack (§4.1.2) by replacing Bob's PQSPK with a key
for which it knows a colliding ciphertext under Bob's secret key. With SH-CR,
any such substitution is detectable, and both parties are guaranteed to have
used the same PQSPK.
:::
