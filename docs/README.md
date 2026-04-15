# PQXDH Documentation Project

Verso-Blueprint documentation for the PQXDH Lean 4 formalization.

Built with [verso-blueprint](https://github.com/ejgallego/verso-blueprint) (v4.28.0),
which extends [Verso](https://github.com/leanprover/verso) with blueprint-style
rendering for mathematical formalizations.

## Dependencies

The docs project (`docs/lakefile.toml`) depends on:

- **versoBlueprint** — documentation framework (fetched from git)
- **PQXDH-lean** — the parent Lean library (via `path = ".."`)

Transitive dependencies (`subverso`, Verso core) are resolved automatically
by Lake from the verso-blueprint manifest. The main project lakefile does
**not** need to list them.

## Building

From the repository root (not from `docs/`):

```bash
# Build the Lean library first
lake build

# Build the documentation executable
lake -d docs build

# Generate HTML and serve locally
./scripts/build-blueprint.sh
python3 -m http.server 8080 -d _out/blueprint
```

Then open http://localhost:8080.

## Project structure

```
docs/
├── lakefile.toml              # Depends on versoBlueprint + parent project
├── lean-toolchain             # Must match parent (v4.28.0)
├── lake-manifest.json         # Pinned dependency versions
├── Main.lean                  # Entry point: CSS, JS, blueprint config
├── PQXDHDocs.lean             # Top-level document definition
└── PQXDHDocs/
    ├── Contents.lean          # Imports all chapters, opens Verso namespaces
    ├── SourceBlock.lean       # Custom code block: extracts proof bodies from source
    ├── DocDH.lean             # Diffie-Hellman
    ├── DocKDF.lean            # Key Derivation Function
    ├── DocAEAD.lean           # Authenticated Encryption
    ├── DocKEM.lean            # Key Encapsulation Mechanism
    ├── DocX3DH.lean           # X3DH Protocol (includes PermDraws + PassiveSecrecy)
    ├── DocPermDraws.lean      # perm_draws Tactic (subsection of X3DH)
    ├── DocX3DHPassiveSecrecy.lean  # Passive Message Secrecy (subsection of X3DH)
    ├── DocPQXDH.lean          # PQXDH Protocol
    └── DocSecurityDefs.lean   # Security Definitions and Assumptions
```

## How it works

- Each `Doc*.lean` file is a Verso document chapter using `#doc (Manual)` blocks.
- Definitions and theorems use `(lean := "DeclarationName")` to link prose
  to Lean declarations, which Verso resolves at elaboration time.
- Proof bodies are extracted via `` ```source DeclarationName `` blocks
  (implemented in `SourceBlock.lean`), which read the actual source file
  and display the proof text.
- Cross-references between chapters use `{uses "tag"}[]` where tags are
  defined by `:::definition` and `:::theorem` blocks.

## Lean version

Both the library and docs must use the same Lean toolchain. Currently
`leanprover/lean4:v4.28.0`, matching Mathlib and verso-blueprint.
