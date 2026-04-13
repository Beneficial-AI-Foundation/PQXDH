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
Formal security definitions and assumptions for PQXDH, following Bhargavan et al.
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
a uniformly random key (section 2.5, assumption 2).
:::

:::definition "kdf_prf" (lean := "KDF_PRF") (parent := "security_defs_core")
The KDF is a pseudorandom function (alternative to the ROM assumption).
:::

:::definition "aead_ind_cpa_int_ctxt" (lean := "AEAD_IND_CPA_INT_CTXT") (parent := "security_defs_core")
AEAD satisfies both IND-CPA and INT-CTXT, which together imply IND-CCA2
(section 2.5, assumption 3).
:::

:::definition "sig_euf_cma" (lean := "Sig_EUF_CMA") (parent := "security_defs_core")
The signature scheme is existentially unforgeable under chosen message attacks
(section 2.5, assumption 5).
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
