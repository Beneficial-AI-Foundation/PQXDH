import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.PQXDH
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "The PQXDH Protocol" =>

:::group "pqxdh"
PQXDH protocol
:::

:::group "pqxdh_correctness"
PQXDH correctness properties.
:::

:::group "symbolic_security"
Symbolic security results (ProVerif).
:::

:::group "computational_security"
Computational security results (CryptoVerif).
:::

:::group "kem_properties"
KEM-specific properties.
:::

PQXDH (Post-Quantum Extended Diffie-Hellman) extends X3DH with a
post-quantum KEM encapsulation. The KEM shared secret is concatenated
into the KDF input alongside the DH shared secrets, providing resistance
to harvest-now-decrypt-later attacks.

Reference: Bhargavan et al. §2.1–§2.3, Figure 1 (USENIX Security 2024).

# Key bundle

Bob's prekey bundle including the post-quantum KEM public key
and signatures authenticating the signed prekeys:

```
structure PQXDHBundle (G PK_kem S_sig : Type _) [AddCommGroup G] where
  IKᵦ : G
  SPKᵦ : G
  sig_spk : S_sig
  OPKᵦ : G
  PQSPK : PK_kem
  sig_pqspk : S_sig
```

# Signature verification

Alice verifies Bob's bundle signatures before proceeding.
This prevents a malicious server from substituting Bob's signed prekeys.

:::definition "PQXDHBundle-verify" (lean := "PQXDHBundle.verify_signatures") (parent := "pqxdh")
Alice verifies both the SPK signature and the PQSPK signature
under Bob's identity public key.
:::

# Shared secret computation

Alice computes the four classical DH values plus the KEM shared secret.

:::definition "PQXDH-Alice" (lean := "PQXDH_Alice") (parent := "pqxdh")
Alice's view of the PQXDH key exchange: four DH values plus the
KEM encapsulation output (ct, ss).
:::

:::definition "PQXDH-Bob" (lean := "PQXDH_Bob") (parent := "pqxdh")
Bob's view of the PQXDH key exchange: four DH values plus the
KEM decapsulation of ct.
:::

# Session key derivation

The session key is derived from the concatenation of all DH outputs
and the KEM shared secret: `SK = KDF(DH1 || DH2 || DH3 || DH4 || ss)`.

:::definition "PQXDH-SK-Alice" (lean := "PQXDH_SK_Alice") (parent := "pqxdh")
Alice derives the PQXDH session key.
:::

:::definition "PQXDH-SK-Bob" (lean := "PQXDH_SK_Bob") (parent := "pqxdh")
Bob derives the PQXDH session key.
:::

# Correctness

:::theorem "PQXDH-agree" (lean := "PQXDH_agree") (parent := "pqxdh_correctness")
If all DH public keys are honestly generated from the same generator,
the bundle is correctly formed, and KEM encaps/decaps are consistent,
then Alice and Bob derive the same PQXDH session key.
:::

:::proof "PQXDH-agree"
By substitution of key generation equations, DH commutativity,
and the KEM encaps/decaps consistency hypothesis.
:::

# Theorem 1 — Symbolic security (ProVerif)

No computational hardness hypotheses are needed — security follows
from the protocol logic alone in the Dolev-Yao model.

:::theorem "PQXDH-symbolic-security" (lean := "PQXDH_symbolic_security") (parent := "symbolic_security")
In the Dolev-Yao model, PQXDH provides:
(1) peer authentication with data agreement,
(2) forward secrecy,
(3) KCI resistance,
(4) session independence, and
(5) HNDL resistance in case of a DH breakdown.
:::

:::proof "PQXDH-symbolic-security"
ProVerif verification of correspondence assertions (Theorems 7, 8, 9 in the paper appendix).
:::

# Theorem 2 — Classical computational security (CryptoVerif)

Assumptions: gapDH + ROM + IND-CPA/INT-CTXT + EUF-CMA.

:::theorem "PQXDH-classical-security" (lean := "PQXDH_classical_security") (parent := "computational_security")
Under gapDH + ROM + IND-CPA/INT-CTXT + EUF-CMA, PQXDH provides
message secrecy and peer authentication with identity/key agreement
(modulo X25519 subgroup elements).
Note: this does NOT guarantee agreement over PQSPK (see Theorem 6).
:::

:::proof "PQXDH-classical-security"
CryptoVerif game-based reduction.
:::

# Theorem 3 — Post-quantum computational security (CryptoVerif)

This theorem makes no assumption about DH. Security rests entirely
on the KEM and KDF.

:::theorem "PQXDH-postquantum-security" (lean := "PQXDH_postquantum_security") (parent := "computational_security")
Under IND-CCA (KEM) + PRF (KDF) + IND-CPA/INT-CTXT (AEAD) +
EUF-CMA (at time of exchange), the session key remains secret
even if DH is broken later. No DH assumption is required.
:::

:::proof "PQXDH-postquantum-security"
CryptoVerif game-based reduction. The `HeldAtExchange` wrapper
reflects that the signature scheme only needs to have been secure
when the session was established.
:::

# Theorem 5 — Kyber is SH-CR (§4)

:::theorem "Kyber-SH-CR" (lean := "Kyber_SH_CR") (parent := "kem_properties")
Kyber-1024 (ML-KEM) satisfies Semi-Honest Collision Resistance (SH-CR)
under the Random Oracle Model for its internal hash functions.
:::

:::proof "Kyber-SH-CR"
Reduction to collision/preimage resistance of Kyber's internal
hash functions under the ROM assumption.
:::

# Theorem 6 — KEM public key agreement (§4)

:::theorem "PQXDH-KEM-pubkey-agreement" (lean := "PQXDH_KEM_pubkey_agreement") (parent := "kem_properties")
Under the classical assumptions plus SH-CR for the KEM, PQXDH provides
extended peer authentication with agreement over the PQSPK (KEM public key).
This strengthens Theorem 2's PeerAuth to {uses "PeerAuthPQ-implies-PeerAuth"}[PeerAuthPQ].
:::

:::proof "PQXDH-KEM-pubkey-agreement"
By combining {uses "PQXDH-classical-security"}[Theorem 2's] authentication
with {uses "Kyber-SH-CR"}[SH-CR] to additionally bind PQSPK.
:::
