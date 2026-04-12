# PQXDH Documentation

[Verso](https://github.com/leanprover/verso)-based documentation for the [PQXDH-lean](https://github.com/Beneficial-AI-Foundation/PQXDH) formalization, rendered with [verso-blueprint](https://github.com/ejgallego/verso-blueprint).

**Live site**: [beneficial-ai-foundation.github.io/PQXDH](https://beneficial-ai-foundation.github.io/PQXDH/)

## Chapters

| Chapter | Source |
|---------|--------|
| Diffie-Hellman | `docs/PQXDHDocs/DocDH.lean` |
| Key Derivation Function | `docs/PQXDHDocs/DocKDF.lean` |
| Authenticated Encryption | `docs/PQXDHDocs/DocAEAD.lean` |
| Key Encapsulation Mechanism | `docs/PQXDHDocs/DocKEM.lean` |
| X3DH Protocol | `docs/PQXDHDocs/DocX3DH.lean` |
| PQXDH Protocol | `docs/PQXDHDocs/DocPQXDH.lean` |
| Security Definitions | `docs/PQXDHDocs/DocSecurityDefs.lean` |
| Passive Message Secrecy | `docs/PQXDHDocs/DocX3DHPassiveSecrecy.lean` |
| `perm_draws` Tactic | `docs/PQXDHDocs/DocPermDraws.lean` |

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.28.0).

```bash
# Build the Lean library
lake build

# Build the documentation site (outputs to _out/blueprint/)
./scripts/build-blueprint.sh
```

To view locally:

```bash
python3 -m http.server 8080 -d _out/blueprint
```

Then open http://localhost:8080.

## Project layout

```
├── PQXDHLean/           # Lean source (library)
├── docs/                # Verso documentation project
│   ├── lakefile.toml    #   docs lakefile (depends on verso-blueprint + parent)
│   ├── Main.lean        #   docs entry point (CSS, JS, config)
│   └── PQXDHDocs/       #   chapter sources + SourceBlock utility
├── scripts/
│   └── build-blueprint.sh
├── lakefile.toml        # Main library lakefile
└── _out/blueprint/      # Generated HTML (git-ignored)
```

## License

See [LICENSE](LICENSE).
