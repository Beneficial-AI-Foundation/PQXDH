# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the main library
lake build

# Build documentation
lake build pqxdhdocs

# Generate blueprint HTML (outputs to _out/blueprint/)
./scripts/build-blueprint.sh
```

## Project Overview

Lean 4 formalization of the PQXDH (Post-Quantum Extended Diffie-Hellman) key agreement protocol, following the USENIX Security 2024 paper by Bhargavan et al. Currently focuses on X3DH, the classical Diffie-Hellman core.

**Status**: Initial specification with correctness proofs. No attacker model or security proofs yet.

## Architecture

The formalization builds up through composition of abstract cryptographic primitives:

```
DH (abstract group operations)
    ↓ X3DH_agree theorem
KDF (DH tuple → session key)
    ↓ X3DH_session_key_agree theorem
AEAD (encrypt/decrypt with SK)
    ↓ X3DH_handshake_correct theorem (end-to-end correctness)
```

### Core Components (PQXDHLean/)

- **DH.lean**: Diffie-Hellman over any `AddCommGroup`. Key property: `DH_comm` (commutativity makes X3DH work)
- **KDF.lean**: Key Derivation Function interface (`derive : I → K`)
- **AEAD.lean**: Authenticated Encryption with Associated Data. Correctness axiom ensures decrypt recovers plaintext
- **KEM.lean**: Key Encapsulation Mechanism for post-quantum layer (not yet integrated into X3DH)
- **X3DH.lean**: Protocol definition with 4-DH computation and three main theorems: `X3DH_agree`, `X3DH_session_key_agree`, `X3DH_handshake_correct`

### Documentation (docs/)

Uses Verso framework with anchor-based code extraction:
- Source files use `-- ANCHOR: name` / `-- ANCHOR_END: name` markers
- Doc files reference anchors via `` ```anchor name `` blocks
- `verso.exampleProject` must be `"."` (workspace root)

## Key Patterns

- All primitives are generic over types (e.g., DH works over any `AddCommGroup`)
- Each primitive structure includes correctness axioms used in downstream proofs
- X3DH protocol theorems compose primitive correctness properties

## Commit Guidelines

- Update documentation (README.md, CLAUDE.md) with every commit to keep it in sync with code changes
