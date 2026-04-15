import VersoManual
import VersoBlueprint
import PQXDHLean.SecurityDefs

open Verso.Genre Manual
open Informal


#doc (Manual) "Security Definitions" =>
%%%
tag := "security_defs"
%%%

:::group "security_defs_core"
Formal security definitions and assumptions for PQXDH, following Bhargavan et al. (USENIX Security 2024).
:::

This chapter collects the security definitions and cryptographic assumptions
used in the PQXDH security analysis (Bhargavan et al., USENIX Security 2024).

Each security property and cryptographic assumption is declared as an
`opaque` definition in Lean. This is a deliberate design choice:
opaque definitions state *what* a security notion requires without
committing to *how* it is realized. This lets the protocol theorems
depend on these assumptions abstractly, so the same proof works for
any concrete instantiation that satisfies the assumption. Opaque
definitions also prevent the simplifier from unfolding security
assumptions during proof search, keeping the proof structure close
to the paper's reasoning.

# Signature scheme

:::definition "sig_keypair" (lean := "SigKeyPair") (parent := "security_defs_core")
A signature key pair: public verification key and private signing key.
:::

:::definition "sig_scheme" (lean := "Sig") (parent := "security_defs_core")
A signature scheme with sign and verify operations, plus an honest
round-trip correctness guarantee.
:::

# Adversary models

:::definition "dolev_yao" (lean := "DolevYao") (parent := "security_defs_core")
The Dolev-Yao adversary model (symbolic/ProVerif). The adversary controls
the network (active MitM) but cryptographic primitives are ideal black boxes.
Security properties are expressed as correspondence assertions. Used in
Theorem 1 (section 3.1).
:::

:::definition "ake_query" (lean := "AKE_Query") (parent := "security_defs_core")
Oracle queries available to the adversary in the computational AKE security
game: `NewSession`, `Send`, `Corrupt`, `RevealSessionKey`, and `Test`.
Models the interface between adversary and challenger in CryptoVerif
(section 3.2).
:::

:::definition "freshness_condition" (lean := "Freshness") (parent := "security_defs_core")
Freshness condition for the AKE security game. A test session is *fresh*
if the adversary has not trivially obtained the answer — e.g., has not
revealed the test/partner session key or corrupted both long-term keys
before session completion (section 3.3).
:::

# Cryptographic assumptions

:::definition "gapdh_hard" (lean := "GapDH_Hard") (parent := "security_defs_core")
The Gap Diffie-Hellman assumption: given a DDH oracle, the CDH problem
remains hard (section 2.5, assumption 1.A).
:::

:::definition "kem_ind_cca" (lean := "KEM_IND_CCA") (parent := "security_defs_core")
KEM IND-CCA security: an attacker who sees the public key and ciphertext
cannot distinguish the shared secret from random, even with a decapsulation
oracle for other ciphertexts (section 2.5, assumption 1.B).
:::

:::definition "kdf_random_oracle" (lean := "KDF_RandomOracle") (parent := "security_defs_core")
The KDF behaves as a random oracle: its output is indistinguishable from
a uniformly random key (section 2.5, assumption 4).
:::

:::definition "kdf_prf" (lean := "KDF_PRF") (parent := "security_defs_core")
The KDF is a pseudorandom function. Used in the post-quantum proof
(Theorem 3) instead of ROM, because CryptoVerif's post-quantum
soundness result does not capture the QROM (section 2.5 and section 3.5).
:::

:::definition "aead_ind_cpa_int_ctxt" (lean := "AEAD_IND_CPA_INT_CTXT") (parent := "security_defs_core")
AEAD satisfies both IND-CPA and INT-CTXT, which together imply IND-CCA2
(section 2.5, assumption 3).
:::

:::definition "sig_euf_cma" (lean := "Sig_EUF_CMA") (parent := "security_defs_core")
The signature scheme is existentially unforgeable under chosen message attacks
(section 2.5, assumption 2).
:::

:::definition "held_at_exchange" (lean := "HeldAtExchange") (parent := "security_defs_core")
Temporal qualification for a cryptographic assumption: the assumption held
at the time the key exchange completed, but may have been broken since
(e.g., by a quantum computer). Used in Theorem 3, where `Sig_EUF_CMA`
is required only at exchange time.
:::

:::definition "kem_sh_cr" (lean := "KEM_SH_CR") (parent := "security_defs_core")
Semi-Honest Collision Resistance (Definition 1, section 4): an adversary
who knows the KEM secret key cannot find a different ciphertext that
decapsulates to the same shared secret. Prevents the KEM re-encapsulation
attack discovered in PQXDH v1.
:::

:::definition "kem_internal_hash_rom" (lean := "KEM_InternalHash_ROM") (parent := "security_defs_core")
The hash functions internal to Kyber (H, G, XOF) behave as Random Oracles.
Distinct from {uses "kdf_random_oracle"}[] — this concerns hashes *inside*
the KEM construction, not the protocol-level KDF. The paper proves Kyber
satisfies SH-CR under this assumption (Theorem 5, section 5.3.2).
:::

# Security properties

:::definition "message_secrecy" (lean := "MessageSecrecy") (parent := "security_defs_core")
Message secrecy: the session key is indistinguishable from random
to a passive adversary, parameterized by a freshness condition.
:::

:::definition "peer_auth" (lean := "PeerAuth") (parent := "security_defs_core")
Peer authentication: if a session completes, the peer's identity key
was used in the computation.
:::

:::definition "peer_auth_pq" (lean := "PeerAuthPQ") (parent := "security_defs_core")
Post-quantum peer authentication: peer authentication under
quantum adversaries, using the KEM layer for additional binding.
:::

:::theorem "peer_auth_pq_implies_peer_auth" (lean := "PeerAuthPQ_implies_PeerAuth") (parent := "security_defs_core") (tags := "security, auth, pq") (effort := "small") (priority := "medium")
Post-quantum peer authentication implies classical peer authentication.
:::

:::definition "forward_secrecy" (lean := "ForwardSecrecy") (parent := "security_defs_core")
Forward secrecy: compromise of long-term keys does not compromise
past session keys.
:::

:::definition "kci_resistance" (lean := "KCI_Resistance") (parent := "security_defs_core")
Key Compromise Impersonation resistance: an adversary who compromises
Alice's long-term key cannot impersonate Bob to Alice.
:::

:::definition "session_independence" (lean := "SessionIndependence") (parent := "security_defs_core")
Session independence: compromise of one session key does not compromise
other session keys.
:::

:::definition "hndl_resistance" (lean := "HNDL_Resistance") (parent := "security_defs_core")
Harvest-Now-Decrypt-Later resistance: a quantum adversary who records
classical transcripts today cannot decrypt them after obtaining a
quantum computer, thanks to the KEM layer.
:::
