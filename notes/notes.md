# Reading Notes: Formal Verification of the PQXDH Post-Quantum Key Agreement Protocol

Bhargavan, Jacomme, Kiefer, Schmidt. USENIX Security 2024.

## Section 2.1: X3DH (Extended Triple Diffie-Hellman)

X3DH is the legacy Signal handshake protocol that PQXDH extends.

### Key Generation

Each agent creates multiple key pairs:

- **IK (Identity Key)**: long-term, never deleted. Think of it as your "passport."
- **SPK (Signed PreKey)**: medium-term, rotated e.g. every two days. Signed by IK so others can verify it's genuine.
- **OPK (One-Time PreKey)**: short-term, deleted after a single use.
- **EK (Ephemeral Key)**: generated fresh per session, deleted immediately after.

### Initiation

Blake (the responder) publishes a "prekey bundle" to a server: his SPK (signed by his IK), and optionally some OPKs. This lets Alex contact Blake even when Blake is offline.

The prekey bundle is a workaround to the fact that a normal Diffie-Hellman key exchange requires both parties to be online simultaneously. Blake pre-computes his DH contributions (SPK, OPKs) and uploads them to a server before any conversation happens. When Alex wants to message Blake — even while Blake's phone is off — she downloads Blake's prekey bundle from the server, generates her own ephemeral key, computes all the DH values, derives the session key, encrypts her message, and sends it via the server. Later, when Blake comes online, he picks up the message, computes the same DH values, derives the same session key, and decrypts.

The tradeoff is trust in the server: you're relying on the server to faithfully deliver Blake's real public keys and not substitute fake ones.

### Session Secret Generation

Alex fetches the bundle, generates her own ephemeral key EK_A, and computes four DH shared secrets:

- **DH1** = DH(IK_A, SPK_B) — proves Alex is Alex (uses her long-term key)
- **DH2** = DH(EK_A, IK_B) — proves Blake is Blake (uses his long-term key)
- **DH3** = DH(EK_A, SPK_B) — forward secrecy (only ephemeral/medium-term keys)
- **DH4** = DH(EK_A, OPK_B) — replay protection (optional, only if OPK available)

All four are fed into a KDF to produce a single session key SK_A, which encrypts the first message via AEAD. The associated data AD includes both identity keys (AD = IK_A || IK_B), binding the ciphertext to both parties' identities.

### Completing the Handshake

Blake performs the same four DH computations (swapping roles) and gets SK_B. By DH commutativity, SK_A = SK_B. He decrypts the AEAD ciphertext to verify.

## Section 2.2: PQXDH Design Rationale

X3DH relies entirely on elliptic curve DH (X25519). A quantum computer running Shor's algorithm can solve discrete logarithms, breaking all four DH values. Any message encrypted today with X3DH could be recorded and decrypted later when quantum computers arrive — this is the **HNDL (Harvest Now, Decrypt Later)** threat.

Signal's response was PQXDH, designed with three goals:

1. **Passive quantum adversary resistance.** The protocol must defend against attackers who can compute discrete logs — specifically, prevent HNDL attacks. This is done by adding a post-quantum KEM (Kyber) to the key exchange.

2. **No security loss.** PQXDH must preserve all of X3DH's classical guarantees (authentication, confidentiality). If the KEM turns out to be broken, users are no worse off than with X3DH alone. This is the "hybrid" approach — security degrades gracefully.

3. **Efficiency.** Minimize changes to Signal's existing codebase and protocol flow. This is a soft goal — they'll trade some efficiency for more security.

An important non-goal: **protection against active quantum adversaries** is explicitly not required. An attacker with a quantum computer who can actively intercept and modify messages in real time could still break authentication (since signatures rely on classical assumptions). This is noted as an open research problem.

The key design choice: rather than replacing X3DH entirely with a fully post-quantum protocol (which would lose all DH-based guarantees), PQXDH is a **hybrid** — it injects a KEM shared secret alongside the DH values into the KDF input. This adds "post-quantum secure entropy," meaning a shared secret that a quantum computer cannot derive or predict. Even if a quantum attacker breaks all four DH values, they still can't compute the KEM shared secret, so the session key retains entropy that is secure against quantum adversaries.

### Kyber-1024 Selection

Signal chose Kyber-1024 (the largest variant in the Kyber family) as the most conservative option. Kyber comes in three security levels:

- Kyber-512: roughly equivalent to AES-128 security
- Kyber-768: roughly equivalent to AES-192 security
- Kyber-1024: roughly equivalent to AES-256 security

"Most conservative" means the strongest variant with the largest security margin. The extra cost (a few hundred extra bytes per handshake) is negligible compared to the long-term protection gained against future advances in lattice cryptanalysis.

## Section 2.3: Protocol Outline

This section describes the concrete changes from X3DH to PQXDH. At a high level, PQXDH injects a post-quantum KEM shared secret into the classical X3DH protocol. The five additions are:

1. **Blake also generates a KEM key pair** (PQSPK) alongside his DH keys, and signs it with his identity key IK_B.

2. **The prekey bundle now includes** PQSPK_B and its signature sign(PQSPK_B, IK_B).

3. **Alex computes a KEM encapsulation**: (CT, SS) = KEM.encaps(PQSPK_B). This produces a KEM ciphertext CT and a shared secret SS. She appends SS to the DH values in the KDF input:
   - SK = KDF(DH1 || DH2 || DH3 || SS)

4. **Alex includes CT** (the KEM ciphertext) in her message to Blake.

5. **Blake decapsulates**: SS = KEM.decaps(CT, PQSPK_B^sk) and appends it to his DH values in the same way.

The only structural change from X3DH is: one extra KEM key pair, one encapsulation/decapsulation, and SS appended to the KDF input. Everything else — the DH computations, the AEAD encryption, the AD construction — stays the same.

Both parties arrive at the same SK because:
- DH commutativity gives the same DH values (as in X3DH)
- KEM correctness gives the same SS

### Simplifications in the Paper

The paper's Figure 1 omits several details for clarity (the full version is in Appendix Figure 4):
- DH4 (the optional OPK computation) is omitted
- No distinction between one-time vs. last-resort KEM keys (all KEM keys treated as medium-term)
- Encoding functions, key identifiers, and the asynchronous server behavior are omitted

## Reading Progress

**Stopped at: end of Section 2.3 (Protocol Outline).** Next: Section 2.4 (Desired Security Properties) and 2.5 (Threat Model and Crypto Assumptions).

**KEM subproject complete:** abstract KEM interface formalized in PQXDHLean/KEM.lean (encaps, decaps, correctness). Key-pair binding kept simple for now — to be refined as needed.

## Main Results (Section 5.2)

**Theorem 1** (Symbolic, ProVerif): PQXDH in the symbolic model provides peer-authentication, forward secrecy, resistance to key compromise impersonation, session independence and resistance to "harvest now decrypt later" attacks in case of a DH break down. In addition, it also provides data agreement over the shared pre-key used.

**Theorem 2** (PQXDH classical computational security, CryptoVerif): If X25519 satisfies the gapDH assumption, the KDF is a Random Oracle, if the AEAD is IND-CPA+INT-CTXT and if the signature scheme is EUF-CMA, then PQXDH guarantees both the secrecy of the sent message, as-well-as peer-authentication with agreement over identities, OPK and SPK used, modulo the subgroup elements of X25519, as well as agreement over the PQSPK used provided it was included in the AD.

**Theorem 3** (PQXDH post-quantum computational security, CryptoVerif): Under IND-CCA for the KEM, if the KDF is a PRF and the final AEAD is IND-CPA+INT-CTXT, as long as the signature scheme was unforgeable when some key exchange was completed, secrecy of the derived key still holds in the future.

Theorem 2 is the classical security result (PQXDH is at least as secure as X3DH). Theorem 3 is the key post-quantum result: even if an attacker later gains access to a quantum computer (breaking DH), the session keys remain secret as long as the KEM (Kyber) is IND-CCA secure. Together they show PQXDH achieves both design goals: no security regression from X3DH, plus HNDL resistance.

---

## Appendix: Cryptographic Concepts

### Entropy

Entropy in cryptography measures how much unpredictability a value has from an attacker's perspective.

- A value with **high entropy** looks completely random to the attacker — they can't guess it or narrow down the possibilities. Example: a 256-bit key generated from a good random source has 256 bits of entropy (2^256 equally likely possibilities).
- A value with **zero entropy** is something the attacker already knows or can compute. Example: a public key posted on a server.

In a key exchange protocol, what matters is the entropy of the session key SK from the attacker's point of view. If SK has high entropy, the attacker can't distinguish it from a random string, so the encrypted messages are secure.

In X3DH, all entropy in SK comes from the DH values — which depend on private keys the attacker doesn't know. But a quantum attacker can compute those private keys from the public keys, so from their perspective SK has zero entropy. PQXDH fixes this by mixing in SS (the KEM shared secret): SK = KDF(DH1 || DH2 || DH3 || DH4 || SS). Even if the quantum attacker computes all four DH values, they still don't know SS, so SK retains entropy from the KEM.

### Passive vs. Active Attackers

A **passive attacker** (eavesdropper) can only observe — they record all messages flowing over the network but cannot modify, delete, inject, or reorder them.

An **active attacker** (man-in-the-middle) can intercept messages and change them — swap public keys, forge messages, replay old ones, etc.

In the HNDL scenario, a passive attacker records the encrypted handshake today and decrypts it later with a quantum computer. PQXDH blocks this because the KEM shared secret can't be broken by quantum algorithms. The paper does not try to protect against an attacker who has a quantum computer today and is actively modifying messages in real time — that would require post-quantum signatures.

### Shor's Algorithm and Discrete Logarithms

Shor's algorithm uses a quantum computer to find the period of modular exponentiation efficiently, which directly reveals the discrete logarithm. This breaks the security assumption underlying Diffie-Hellman key exchange.

### AES (Advanced Encryption Standard)

AES is the most widely used symmetric encryption algorithm. "Symmetric" means the same key encrypts and decrypts. AES comes in three key sizes — 128, 192, and 256 bits — where larger keys mean more security. AES-256 is considered secure even against quantum computers (Grover's algorithm only halves the effective key length, so AES-256 still provides 128-bit quantum security).

In PQXDH, AES appears as the AEAD scheme: AES-256 in CBC mode with HMAC (Encrypt-Then-Mac) encrypts Alice's first message using the session key SK.

### Session

A session is one complete run of the key exchange protocol between Alice and Bob, producing one session key SK. Each session produces a fresh, independent SK. If Alice messages Bob again tomorrow, that's a new session with a new ephemeral key, new DH values, and a new SK. The session key is ephemeral — after the handshake, SK is fed into the Double Ratchet protocol for ongoing communication, and the raw DH values are deleted. Compromising one session key doesn't reveal other sessions' keys (session independence).

### Diffie-Hellman (DH)

A method for two parties to establish a shared secret over an insecure channel. Each party picks a private scalar and publishes the corresponding public key (scalar times a generator point). The shared secret is computed by multiplying one's own private scalar with the other's public key. DH commutativity ensures both parties arrive at the same value.

#### Security Properties of DH

DH has two layers of properties: algebraic properties (proven in the Lean formalization) and computational hardness assumptions (believed but unprovable).

**Algebraic properties** (proven in DH.lean):
- **Commutativity**: DH(a, DH(b, P)) = DH(b, DH(a, P)) — enables Alice and Bob to compute the same shared secret.
- **Associativity**: DH(a, DH(b, B)) = DH(a·b, B) — iterated scalar multiplication collapses.
- **Distributivity**: DH(a+b, B) = DH(a, B) + DH(b, B) — scalar addition distributes over the group operation.

**Computational hardness assumptions** (not proven, relied upon for security):
- **DLP (Discrete Logarithm Problem)**: Given B = DH(a, G), recovering `a` is infeasible. This makes public keys safe to publish.
- **CDH (Computational Diffie-Hellman)**: Given DH(a, G) and DH(b, G), computing DH(a, DH(b, G)) without knowing `a` or `b` is infeasible. This makes the shared secret actually secret.
- **DDH (Decisional Diffie-Hellman)**: Given DH(a, G), DH(b, G), and some C, distinguishing whether C = DH(a, DH(b, G)) or C is random is infeasible. This provides indistinguishability — an eavesdropper can't even tell if they're looking at the real shared secret.

The Lean formalization proves only correctness (both parties agree) from the algebraic properties. The hardness assumptions live outside the type system and would require a computational model (CryptoVerif, EasyCrypt) to formalize.

### KDF (Key Derivation Function)

A deterministic function that derives a fixed-size cryptographic key from variable-length input material. In PQXDH the concrete instantiation is HKDF (HMAC-based KDF, RFC 5869) with SHA-256. The security assumption is that the KDF behaves as a random oracle: its output is indistinguishable from a uniformly random key.

### AEAD (Authenticated Encryption with Associated Data)

Provides both confidentiality (plaintext is secret) and integrity (ciphertext can't be tampered with) for a message, while binding the ciphertext to unencrypted associated data. In PQXDH the concrete instantiation is AES-256 in CBC mode with HMAC. The security assumptions are IND-CPA (ciphertexts reveal nothing about the plaintext) and INT-CTXT (an adversary cannot forge a valid ciphertext).

### KEM (Key Encapsulation Mechanism)

A public-key primitive for establishing a shared secret. One party "encapsulates" to produce a ciphertext and a shared secret; the other "decapsulates" the ciphertext with their private key to recover the same shared secret. PQXDH uses Kyber (a lattice-based post-quantum KEM) which is secure under the Module-LWE assumption — believed to be hard even for quantum computers.

### Module-LWE (Module Learning With Errors)

LWE (Learning With Errors) is a mathematical problem: given a system of linear equations over integers with small random errors added, recover the secret values. Without the errors, this is just solving a linear system (easy). With errors, it becomes extremely hard — and believed to be hard even for quantum computers.

Module-LWE is a structured variant where the equations are organized into modules over polynomial rings. This makes the key sizes smaller and operations faster compared to plain LWE, while preserving the hardness.

A rough analogy:

- **Discrete log** (what DH relies on): "I tell you g and g^x; find x." Easy for quantum computers (Shor's algorithm).
- **Module-LWE** (what Kyber relies on): "I tell you A and A*s + e, where e is small noise; find s." No known quantum algorithm solves this efficiently.

Kyber's key generation, encapsulation, and decapsulation are all built on Module-LWE operations. The security proof shows that breaking Kyber requires solving Module-LWE, which is the best evidence we have that it's post-quantum secure.

### GapDH (Gap Diffie-Hellman Assumption)

The assumption that computing DH shared secrets is hard, even when given access to a DDH oracle (an oracle that can check whether a given tuple is a valid DH tuple). This is the standard computational assumption for X25519.

### IND-CCA (Indistinguishability under Chosen-Ciphertext Attack)

A security notion meaning an attacker who can decrypt other ciphertexts still can't distinguish encryptions of two chosen plaintexts. This is the standard security requirement for KEMs.

### Digital Signatures (Signing a Key with Another Key)

When we say "Blake signs PQSPK_B with IK_B," what happens is:

1. Blake takes the data to be signed (the encoding of PQSPK_B's public key).
2. He uses his identity private key IK_B^sk to compute a signature — a short string that acts as proof that he (the owner of IK_B) endorses this data.
3. Anyone who knows IK_B^pk (his public identity key) can verify the signature, confirming that the data hasn't been tampered with and was indeed signed by the holder of IK_B^sk.

The concrete algorithm in Signal is XEdDSA — an EdDSA-style signature scheme that reuses X25519 key pairs for signing. The signature doesn't hide the data (anyone can read PQSPK_B^pk), it just binds it to Blake's identity.

The key difference from encryption:
- **Encryption**: uses the recipient's *public* key to hide data; only the recipient's *private* key can recover it.
- **Signing**: uses the signer's *private* key to produce a proof; anyone with the signer's *public* key can verify it.

The purpose in PQXDH is authentication of the prekey bundle: when Alex downloads Blake's PQSPK_B from the server, she verifies the signature against IK_B^pk. If the server (or an attacker) substituted a fake key, the signature check would fail and Alex would abort the protocol.

### EUF-CMA (Existential Unforgeability under Chosen-Message Attack)

Signatures cannot be forged even if the attacker can obtain signatures on arbitrary other messages. This is the standard security requirement for digital signature schemes.
