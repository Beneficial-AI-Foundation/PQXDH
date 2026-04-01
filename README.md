# PQXDH-lean

A Lean 4 formalization of the PQXDH (Post-Quantum Extended Diffie-Hellman) key agreement protocol, following the presentation in:

> K. Bhargavan, C. Jacomme, F. Kiefer, and R. Schmidt. *Formal verification of the PQXDH Post-Quantum key agreement protocol for end-to-end secure messaging.* USENIX Security 2024. [[PDF]](https://www.usenix.org/system/files/usenixsecurity24-bhargavan.pdf)

PQXDH extends X3DH by adding post-quantum resistance via a Key Encapsulation Mechanism (KEM). The current formalization focuses on X3DH, the classical Diffie-Hellman core of PQXDH, with both **correctness proofs** and an initial **security proof** under the Random Oracle Model.

## Main results

### Correctness

- **DH commutativity** (`DH_comm`): the algebraic property that makes X3DH work — Alice and Bob compute the same shared secrets.
- **X3DH correctness** (`X3DH_agree`): if all public keys are honestly generated from the same generator, Alice and Bob compute identical DH tuples.
- **Session key agreement** (`X3DH_session_key_agree`): both parties derive the same session key via KDF.
- **Handshake correctness** (`X3DH_handshake_correct`): end-to-end theorem composing DH agreement, KDF, and AEAD — Bob can decrypt Alice's first message.

### Security

- **Passive message secrecy** (`passive_secrecy_le_ddh`): a passive eavesdropper's advantage in distinguishing the real session key from a random key is bounded by the DDH advantage against a concrete reduction. This is a tight bound (no factor of 2) under the Random Oracle Model for the KDF, proved via a two-game formulation with distributional equivalences between the passive games and the DDH experiments.

The security proof uses the [VCV-io](https://github.com/Verified-zkEVM/VCV-io) library for oracle computations, random oracle semantics, and the DDH hardness assumption.

## Structure

| File                                            | Description |
|-------------------------------------------------|-------------|
| `PQXDHLean/X3DH/DH.lean`                       | Abstract Diffie-Hellman over any `AddCommGroup` |
| `PQXDHLean/X3DH/X3DH.lean`                     | X3DH protocol: shared secret, session key, handshake correctness |
| `PQXDHLean/X3DH/X3DHPassiveMessageSecrecy.lean` | Passive secrecy game, DDH reduction, and security theorem |
| `PQXDHLean/KDF.lean`                            | Key Derivation Function interface |
| `PQXDHLean/AEAD.lean`                           | Authenticated Encryption with Associated Data |
| `PQXDHLean/KEM.lean`                            | Key Encapsulation Mechanism interface |
| `PQXDHLean/Tactics/PermDraws.lean`              | `perm_draws` tactic for distributional equivalences |
| `PQXDHLean/PQXDH.lean`                          | PQXDH protocol definition (stub) |
| `PQXDHLean/Examples/X3DHExample.lean`            | Concrete example instantiation |

## Architecture

The formalization builds up through composition of abstract cryptographic primitives:

```
DH (abstract group operations)
    | X3DH_agree theorem
KDF (DH tuple -> session key)
    | X3DH_session_key_agree theorem
AEAD (encrypt/decrypt with SK)
    | X3DH_handshake_correct theorem (end-to-end correctness)

DDH assumption + Random Oracle Model
    | passiveReal_eq_ddhExpReal, passiveRand_eq_ddhExpRand
    | passive_secrecy_le_ddh theorem (security)
```

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.28.0).

```bash
lake build
```

## Documentation

The `docs/` directory contains a [Verso](https://github.com/leanprover/verso)-based literate document with prose explanations and verified code excerpts.

To build the documentation blueprint:

```bash
./scripts/build-blueprint.sh
```

To view the generated documentation locally:

```bash
python3 -m http.server 8080 -d _out/blueprint
```

Then open http://localhost:8080 in your browser.

## License

See [LICENSE](LICENSE).
