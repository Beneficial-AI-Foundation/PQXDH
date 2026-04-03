import VersoManual
import VersoBlueprint

open Verso.Genre Manual
open Informal

#doc (Manual) "From X3DH to PQXDH" =>
%%%
tag := "pqxdh"
%%%

:::group "pqxdh_core"
Roadmap items for extending the current X3DH development to the full PQXDH protocol.
:::

This chapter records only the extension path already stated in the local docs.
The introduction says that the current formalization focuses on X3DH as a
stepping stone toward PQXDH. The KEM chapter says that Alice appends the KEM
shared secret to her KDF input and Bob recovers the same secret by decapsulation.
The X3DH chapter says that both parties already agree on the classical X3DH
tuple and derive their session key from a KDF.

:::definition "pqxdh_transcript" (parent := "pqxdh_core")
A PQXDH transcript consists of the agreed X3DH Diffie-Hellman tuple together
with the post-quantum shared secret recovered through {uses "kem_spec"}[], all
of which is passed to {uses "kdf_spec"}[] for final session-key derivation.
:::

Conceptually, Alice computes the classical X3DH tuple, encapsulates to Bob's
post-quantum public key, and appends the resulting shared secret to her KDF
input. Bob computes the same classical tuple, decapsulates the KEM ciphertext,
and appends the recovered shared secret to his own KDF input.

:::theorem "pqxdh_classical_component_agree" (parent := "pqxdh_core") (tags := "pqxdh, roadmap, classical") (effort := "small") (priority := "high")
The classical component of the future PQXDH transcript already agrees because
the current development proves {uses "x3dh_agree"}[].
:::

:::proof "pqxdh_classical_component_agree"
Reuse {uses "x3dh_agree"}[] unchanged: PQXDH keeps the same classical X3DH
Diffie-Hellman tuple as its classical input.
:::

:::theorem "pqxdh_post_quantum_component_agree" (parent := "pqxdh_core") (tags := "pqxdh, roadmap, pq") (effort := "small") (priority := "high")
The post-quantum component agrees whenever the KEM round-trip satisfies
{uses "kem_decaps_encaps"}[].
:::

:::proof "pqxdh_post_quantum_component_agree"
The KEM chapter already isolates the needed statement: Alice gets a shared
secret from encapsulation, Bob gets the same secret by decapsulation, and that
value is the post-quantum contribution to the KDF input.
:::

:::theorem "pqxdh_combined_transcript_agree" (parent := "pqxdh_core") (tags := "pqxdh, roadmap, transcript") (effort := "medium") (priority := "high")
If the classical component agrees by {uses "pqxdh_classical_component_agree"}[]
and the post-quantum component agrees by
{uses "pqxdh_post_quantum_component_agree"}[], then the full transcript from
{uses "pqxdh_transcript"}[] agrees on both sides.
:::

:::proof "pqxdh_combined_transcript_agree"
Pair the common X3DH tuple with the common KEM shared secret. The resulting
combined KDF input is then identical for Alice and Bob.
:::

:::theorem "pqxdh_session_key_agree" (parent := "pqxdh_core") (tags := "pqxdh, roadmap, kdf") (effort := "small") (priority := "high")
If both parties feed the same combined transcript from
{uses "pqxdh_combined_transcript_agree"}[] into {uses "kdf_spec"}[], then they
derive the same PQXDH session key.
:::

:::proof "pqxdh_session_key_agree"
Use {uses "pqxdh_combined_transcript_agree"}[] to identify the full KDF input
on both sides. Since {uses "kdf_spec"}[] is modeled as a deterministic derive
function, equal inputs produce equal session keys.
:::

:::theorem "pqxdh_handshake_roadmap" (parent := "pqxdh_core") (tags := "pqxdh, roadmap, handshake") (effort := "medium") (priority := "high")
A complete PQXDH handshake theorem should reuse the structure of
{uses "x3dh_handshake_correct"}[] after replacing the X3DH-only session key with
the combined transcript described by {uses "pqxdh_transcript"}[] and the key
agreement step described by {uses "pqxdh_session_key_agree"}[].
:::

:::proof "pqxdh_handshake_roadmap"
The existing authentication argument in {uses "x3dh_handshake_correct"}[] already
isolates the AEAD step. The main remaining work is to formalize the combined
PQXDH key schedule and prove its agreement using
{uses "pqxdh_session_key_agree"}[].
:::
