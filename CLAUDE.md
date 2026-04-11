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

**Status**: X3DH correctness proofs complete. Passive message secrecy proved (tight DDH reduction under ROM). No active adversary model yet.

## Architecture

The formalization is organized into abstract signatures and two proof
models (symbolic and computational), each with a framework-agnostic
core and optional framework-specific instantiations. Replacing the
proof framework (e.g. VCVio) only requires changes in the
framework-specific layers (2.x.2).

### 1. Abstract signature definitions

Framework-independent algebraic definitions of cryptographic primitives.
Each structure is parameterized over abstract types, carries deterministic
operations, and includes correctness axioms. No imports from VCVio,
Mathlib probability, or any specific computational framework.

| File | Primitive | Key operation |
|------|-----------|---------------|
| **X3DH/DH.lean** | Diffie-Hellman | `DH a B = a • B` over any `AddCommGroup` with `Module F G` |
| **KDF.lean** | Key Derivation Function | `derive : I → K` |
| **KEM.lean** | Key Encapsulation Mechanism | `encaps : PK → CT × SS`, `decaps : SK → CT → SS` |
| **AEAD.lean** | Authenticated Encryption | `encrypt`, `decrypt` with correctness axiom |
| **SecurityDefs.lean** | Signature scheme, adversary types | `Sig`, `Freshness`, `DolevYao`, `AKE_Query` |

### 2. Models

#### 2.1 Symbolic model (ProVerif-style)

- **2.1.1 General**: Theorem 1 statement, Dolev-Yao adversary, symbolic
  security properties. No framework needed — security follows from
  protocol logic alone.
- **2.1.2 Framework-specific**: Empty today. Would hold ProVerif-style
  reasoning if formalized in Lean.

#### 2.2 Computational model (CryptoVerif-style)

- **2.2.1 General (framework-agnostic)**: Security games, reductions,
  and theorem statements parameterized over an abstract `ProbMonad`
  typeclass. Game definitions (HNDL, IND-CCA, PRF), adversary types,
  advantages, and reductions are all defined over an abstract `M` —
  no VCVio dependency. Correctness proofs (`PQXDH_agree`, `X3DH_agree`)
  also belong here.

- **2.2.2 Framework-specific (VCVio)**: `ProbMonad` instance for VCVio's
  `ProbComp`. Adapters bridging abstract signatures to VCVio types
  (`KDFOracle`, KEM→`KEMScheme`, KDF→`PRFScheme`). Proof automation
  (`perm_draws` tactic). Concrete proofs that instantiate the abstract
  games and discharge obligations using VCVio's machinery.

### Design invariants

- Abstract signature files (Layer 1) never import VCVio or any probability framework.
- Layer 2.2.1 files only depend on the `ProbMonad` typeclass, not VCVio.
- Replacing VCVio only requires changes in 2.1.2/2.2.2.
- Opaque `Prop` security definitions are temporary placeholders to be
  replaced by concrete game definitions in 2.2.1, instantiated in 2.2.2.

### Current file mapping

```
1. Abstract signatures:
   DH.lean, KDF.lean, KEM.lean, AEAD.lean, SecurityDefs.lean (structures)
   PQXDH.lean (protocol definition: PQXDHBundle, PQXDH_Alice, PQXDH_Bob)

2.2.1 General computational:
   X3DH/X3DH.lean (correctness proofs)
   PQXDH.lean (PQXDH_agree, security theorem statements)

2.2.2 VCVio-specific:
   KDF.lean (KDFOracle — needs to be moved out)
   X3DH/X3DHPassiveMessageSecrecy.lean (passive secrecy proof)
   Tactics/PermDraws.lean (perm_draws tactic)
```

### Other components

- **Tactics/PermDraws.lean**: `perm_draws` tactic — automatically proves distributional equivalences between computations that differ only in the order of independent uniform draws
- **Examples/X3DHExample.lean**: Concrete instantiation of X3DH over ℚ

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
