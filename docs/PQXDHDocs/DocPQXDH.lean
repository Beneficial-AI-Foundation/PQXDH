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
adding a post-quantum KEM layer. Alice appends the KEM shared secret to her
KDF input, and Bob recovers the same secret by decapsulation. The resulting
session key depends on both classical DH and post-quantum KEM contributions.

# Protocol bundle

:::definition "pqxdh_bundle" (lean := "PQXDHBundle") (parent := "pqxdh_core")
A PQXDH bundle packages all public values that Bob publishes to the server:
identity key, signed pre-key, one-time pre-key, post-quantum signed pre-key,
and associated signatures. Signature verification is included as a method.
:::

# Shared secret computation

:::definition "pqxdh_alice" (lean := "PQXDH_Alice") (parent := "pqxdh_core")
Alice computes the extended DH tuple, including the classical X3DH components
and the post-quantum KEM encapsulation.
:::

:::definition "pqxdh_bob" (lean := "PQXDH_Bob") (parent := "pqxdh_core")
Bob computes the same extended DH tuple, using his private keys and the KEM
decapsulation.
:::

# Session key derivation

:::definition "pqxdh_sk_alice" (lean := "PQXDH_SK_Alice") (parent := "pqxdh_core")
Alice's PQXDH session key: {uses "kdf_spec"}[] applied to the combined
classical and post-quantum transcript.
:::

:::definition "pqxdh_sk_bob" (lean := "PQXDH_SK_Bob") (parent := "pqxdh_core")
Bob's PQXDH session key: {uses "kdf_spec"}[] applied to his combined
transcript.
:::

# Agreement

:::theorem "pqxdh_agree" (lean := "PQXDH_agree") (parent := "pqxdh_core") (tags := "pqxdh, agreement") (effort := "medium") (priority := "high")
If all key pairs are honestly generated and the KEM round-trip succeeds,
then Alice and Bob derive the same PQXDH session key. Composes
{uses "x3dh_agree"}[] with {uses "kem_spec"}[] correctness.
:::

# Security properties

:::theorem "pqxdh_symbolic_security" (lean := "PQXDH_symbolic_security") (parent := "pqxdh_core") (tags := "pqxdh, security, symbolic") (effort := "large") (priority := "high")
Symbolic security of PQXDH: under the Dolev-Yao attacker model,
the protocol satisfies message secrecy and peer authentication.
:::

:::theorem "pqxdh_classical_security" (lean := "PQXDH_classical_security") (parent := "pqxdh_core") (tags := "pqxdh, security, classical") (effort := "large") (priority := "high")
Classical computational security: under Gap-DH, KDF-as-random-oracle,
and AEAD IND-CPA + INT-CTXT assumptions, the protocol achieves
message secrecy and forward secrecy.
:::

:::theorem "pqxdh_postquantum_security" (lean := "PQXDH_postquantum_security") (parent := "pqxdh_core") (tags := "pqxdh, security, postquantum") (effort := "large") (priority := "high")
Post-quantum security: under KEM IND-CCA and additional assumptions,
the protocol achieves message secrecy even against quantum adversaries.
:::

:::theorem "pqxdh_kem_pubkey_agreement" (lean := "PQXDH_KEM_pubkey_agreement") (parent := "pqxdh_core") (tags := "pqxdh, kem, agreement") (effort := "small") (priority := "medium")
The KEM public key used by Alice for encapsulation agrees with
Bob's published post-quantum signed pre-key.
:::
