# PQXDH-lean

A Lean 4 formalization of the PQXDH (Post-Quantum Extended Diffie-Hellman) key agreement protocol, following the presentation in:

> K. Bhargavan, C. Jacomme, F. Kiefer, and R. Schmidt. *Formal verification of the PQXDH Post-Quantum key agreement protocol for end-to-end secure messaging.* USENIX Security 2024. [[PDF]](https://www.usenix.org/system/files/usenixsecurity24-bhargavan.pdf)

PQXDH extends X3DH by adding post-quantum resistance via a Key Encapsulation Mechanism (KEM). In the current state of this formalization we focus on X3DH, as it is a central component of PQXDH: X3DH provides the classical Diffie-Hellman core on top of which the post-quantum KEM layer is composed. Understanding and verifying X3DH first is therefore a necessary stepping stone toward the full PQXDH protocol.

This is an initial specification — not a complete formalization. We declare algebraic (dependent-typed) signatures for the main components of the protocol. There is no attacker model, and no security properties are stated or proved. The main purpose is to show how the protocol can be specified in a way that is close to the description in the paper, and to show how the different components (DH, KDF, AEAD) fit together.

## Structure

| File | Description |
|------|-------------|
| `PQXDHLean/DH.lean` | Abstract Diffie-Hellman over any `AddCommGroup`, with commutativity, associativity, and distributivity lemmas |
| `PQXDHLean/KDF.lean` | Abstract Key Derivation Function interface |
| `PQXDHLean/AEAD.lean` | Abstract Authenticated Encryption with Associated Data, with correctness theorems |
| `PQXDHLean/KEM.lean` | Abstract Key Encapsulation Mechanism interface, with correctness theorem |
| `PQXDHLean/X3DH.lean` | X3DH protocol: Alice/Bob shared secret computation, session key derivation, and end-to-end handshake correctness |

## Main results

- **DH commutativity** (`DH_comm`): the algebraic property that makes X3DH work — Alice and Bob compute the same shared secrets.
- **X3DH correctness** (`X3DH_agree`): if all public keys are honestly generated from the same generator, Alice and Bob compute identical DH tuples.
- **Session key agreement** (`X3DH_session_key_agree`): both parties derive the same session key via KDF.
- **Handshake correctness** (`X3DH_handshake_correct`): end-to-end theorem composing DH agreement, KDF, and AEAD — Bob can decrypt Alice's first message.

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.29.0-rc3) and [Mathlib](https://github.com/leanprover-community/mathlib4).

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
