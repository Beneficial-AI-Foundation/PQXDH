# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Build the main library
lake build

# Build documentation
lake -d docs build

# Generate blueprint HTML (outputs to _out/blueprint/)
./scripts/build-blueprint.sh
```

## Project Overview

Lean 4 formalization of the PQXDH (Post-Quantum Extended Diffie-Hellman) key agreement protocol, following the USENIX Security 2024 paper by Bhargavan et al. Currently focuses on X3DH, the classical Diffie-Hellman core.

**Status**: X3DH correctness proofs complete. Passive message secrecy theorem stated with tight DDH reduction, but `execGame` uses `uniformSampleImpl` instead of `randomOracle`, making the bound vacuously true (see known limitation below). No active adversary model yet.

## Architecture

The formalization builds up through composition of abstract cryptographic primitives:

```
── X3DH (classical core) ──────────────────────────────────
DH (abstract group operations)
    ↓ X3DH_agree theorem
KDF (DH tuple → session key)
    ↓ X3DH_session_key_agree theorem
AEAD (encrypt/decrypt with SK)
    ↓ X3DH_handshake_correct theorem (end-to-end correctness)

DDH assumption + Random Oracle Model
    ↓ passiveReal_eq_ddhExpReal, passiveRand_eq_ddhExpRand
    ↓ passive_secrecy_le_ddh theorem (security)

── PQXDH (post-quantum extension) ─────────────────────────
X3DH + KEM (post-quantum KEM layer)
    ↓ PQXDH_agree theorem (correctness)
SecurityDefs (GapDH, KEM IND-CCA, KDF ROM/PRF, AEAD, Sig)
    ↓ PQXDH_symbolic_security       (Theorem 1, Dolev-Yao)
    ↓ PQXDH_classical_security      (Theorem 2, computational)
    ↓ PQXDH_postquantum_security    (Theorem 3, HNDL)
```

### Core Components (PQXDHLean/)

- **X3DH/DH.lean**: Diffie-Hellman over any `AddCommGroup`. Key property: DH commutativity (via `smul_smul` + `mul_comm` from Mathlib)
- **X3DH/X3DH.lean**: Protocol definition with 4-DH computation and three main theorems: `X3DH_agree`, `X3DH_session_key_agree`, `X3DH_handshake_correct`
- **X3DH/X3DHPassiveMessageSecrecyUniform.lean**: Passive secrecy game, DDH reduction, distributional equivalences, and `passive_secrecy_le_ddh` theorem using `uniformSampleImpl`. **Known limitation:** `execGame` uses stateless fresh samples instead of `randomOracle` (lazy cached ROM), collapsing the real/random distinction and making the theorem vacuously true
- **X3DH/X3DHPassiveMessageSecrecyROM.lean**: ROM-based passive secrecy definitions with `execGame` using VCVio's `randomOracle` (lazy cached sampling). Security proofs require game-hopping infrastructure that VCVio is still developing (cf. `Examples/BR93.lean`)
- **KDF.lean**: Key Derivation Function interface (`derive : I → K`)
- **AEAD.lean**: Authenticated Encryption with Associated Data. Correctness axiom ensures decrypt recovers plaintext
- **KEM.lean**: Key Encapsulation Mechanism for post-quantum layer
- **PQXDH.lean**: PQXDH protocol extending X3DH with KEM. Security theorems stated with `sorry` (match CryptoVerif/ProVerif results)
- **SecurityDefs.lean**: Cryptographic assumptions (GapDH, KEM IND-CCA, KDF ROM/PRF, AEAD, Sig EUF-CMA), adversary models (Dolev-Yao, AKE), and security properties
- **Examples/X3DHExample.lean**: Concrete X3DH protocol run over rationals
- **Tactics/PermDraws.lean**: `perm_draws` tactic — automatically proves distributional equivalences between computations that differ only in the order of independent uniform draws

### Documentation (docs/)

Uses Verso Blueprint framework with source-based code extraction:
- Doc files use `` ```source DeclarationName `` blocks to extract proof bodies from Lean source
- `SourceBlock.lean` resolves declarations by name, finds the module, and reads the source file
- Build: `lake -d docs build` compiles the documentation; `./scripts/build-blueprint.sh` generates HTML

## Key Patterns

- All primitives are generic over types (e.g., DH works over any `AddCommGroup`)
- Each primitive structure includes correctness axioms used in downstream proofs
- X3DH protocol theorems compose primitive correctness properties

## Commit Guidelines

- Update documentation (README.md, CLAUDE.md) with every commit to keep it in sync with code changes
- **Never perform destructive or shared-state actions** (push, force-push, revert, delete branches, modify branches other than the current working branch, etc.) **without explicitly asking for confirmation first.**
