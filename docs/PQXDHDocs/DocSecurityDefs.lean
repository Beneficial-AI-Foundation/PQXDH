import Verso
import VersoManual
import VersoBlueprint
import PQXDHLean.SecurityDefs
open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal
set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "Security Definitions" =>

:::group "security_defs"
Cryptographic security definitions.
:::

:::group "adversary_models"
Adversary models for protocol analysis.
:::

:::group "hardness_assumptions"
Cryptographic hardness assumptions (§2.5).
:::

:::group "security_properties"
Protocol security properties.
:::

Security definitions for the PQXDH main result, formalizing
the cryptographic assumptions, adversary models, and security
games from Bhargavan, Jacomme, Kiefer, Schmidt (USENIX Security 2024).

Security properties in cryptography are defined relative to a
security game played between a challenger and an adversary.
Since Lean cannot express computational complexity bounds, we model
each hardness assumption as an opaque `Prop` whose internal structure
documents the game but whose truth is axiomatically assumed when needed.

# Signature scheme

```
structure SigKeyPair (PK_sig SK_sig : Type _) where
  pk : PK_sig
  sk : SK_sig
```

```
structure Sig (PK_sig SK_sig M S : Type _) where
  keygen : SigKeyPair PK_sig SK_sig
  sign : SK_sig → M → S
  verify : PK_sig → M → S → Bool
  correctness : ∀ (m : M), verify keygen.pk m (sign keygen.sk m) = true
```

# Adversary models

The paper analyzes PQXDH under two adversary models:
a symbolic (Dolev-Yao) model for ProVerif analysis and
a computational (game-based) model for CryptoVerif analysis.

The Dolev-Yao adversary controls the network (active MitM) but treats
cryptographic primitives as ideal black boxes. No computational hardness
assumptions appear — security follows from the protocol logic alone.

```
inductive DolevYao where
  | mk
```

The computational model uses oracle queries available to the adversary
in the authenticated key exchange (AKE) security game:

```
inductive AKE_Query where
  | NewSession
  | Send
  | Corrupt
  | RevealSessionKey
  | Test
```

A freshness condition rules out trivial wins in the AKE game:

```
structure Freshness where
  no_reveal_test : Prop
  no_reveal_partner : Prop
  no_dual_corruption_before_completion : Prop
```

# Hardness assumptions (§2.5)

Each assumption models a specific security game, defined as an opaque `Prop`.

`GapDH_Hard` (Assumption 1.A): the gap Diffie-Hellman problem is hard on X25519.

`KEM_IND_CCA` (Assumption 1.B): the KEM is IND-CCA.
The adversary must distinguish a real shared secret from random, even with a decapsulation oracle.

`KDF_RandomOracle` (Assumption 2, classical): the KDF behaves as a Random Oracle.

`KDF_PRF` (Assumption 2, post-quantum): the KDF is a pseudorandom function.
Used in the post-quantum proof because CryptoVerif's PQ soundness does not capture QROM.

`AEAD_IND_CPA_INT_CTXT` (Assumption 3): the AEAD scheme is IND-CPA + INT-CTXT,
which together imply IND-CCA2.

`Sig_EUF_CMA` (Assumption 4): the signature scheme is existentially
unforgeable under chosen-message attack.

`HeldAtExchange`: a temporal wrapper indicating an assumption held
at the time the key exchange completed, but may have been broken since
(e.g. by a quantum computer).

# Semi-honest collision resistance (§4)

A new KEM security property introduced by the paper to address the
KEM re-encapsulation attack discovered in PQXDH v1.

A malicious server could replace Bob's PQSPK with a different key pk'
while keeping Bob's secret key sk unchanged. SH-CR ensures this cannot
happen: any ciphertext that decapsulates correctly under sk must be the
one honestly generated for the matching public key.

`KEM_SH_CR` (Definition 1): the adversary, knowing sk, cannot find a
different ciphertext that decapsulates to the same shared secret.

`KEM_InternalHash_ROM`: Kyber's internal hash functions (H, G, XOF) behave
as Random Oracles. Used in the proof that Kyber satisfies SH-CR.

# Security properties

:::definition "MessageSecrecy" (lean := "MessageSecrecy") (parent := "security_properties")
The session key is indistinguishable from random for any fresh adversary
in the AKE game.
:::

:::definition "PeerAuth" (lean := "PeerAuth") (parent := "security_properties")
Peer authentication with identity and key agreement: both parties agree on
IKₐ, IKᵦ, SPKᵦ, OPKᵦ (but not necessarily PQSPK).
:::

:::definition "PeerAuthPQ" (lean := "PeerAuthPQ") (parent := "security_properties")
Extended peer authentication: PeerAuth plus agreement over PQSPK (KEM public key).
Requires the additional SH-CR assumption on the KEM.
:::

:::theorem "PeerAuthPQ-implies-PeerAuth" (lean := "PeerAuthPQ_implies_PeerAuth") (parent := "security_properties")
PeerAuthPQ implies PeerAuth: PQSPK agreement is strictly stronger.
:::

:::proof "PeerAuthPQ-implies-PeerAuth"
PeerAuthPQ adds one more agreed parameter on top of PeerAuth.
:::

:::definition "ForwardSecrecy" (lean := "ForwardSecrecy") (parent := "security_properties")
Even if all long-term identity keys are compromised after a session completes,
the session key remains indistinguishable from random.
:::

:::definition "KCI-Resistance" (lean := "KCI_Resistance") (parent := "security_properties")
Compromise of Alice's identity key does not allow impersonating Bob to Alice.
:::

:::definition "SessionIndependence" (lean := "SessionIndependence") (parent := "security_properties")
Compromise of one session key does not help attack a different session.
:::

:::definition "HNDL-Resistance" (lean := "HNDL_Resistance") (parent := "security_properties")
Harvest-Now-Decrypt-Later resistance: a passive quantum adversary who records
all ciphertexts today cannot recover session keys when a quantum computer
becomes available, provided the KEM remains IND-CCA.
:::
