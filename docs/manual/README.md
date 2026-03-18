# X3DH in Lean — Documentation

This directory contains the [Verso](https://github.com/leanprover/verso)-based literate documentation for the PQXDH-lean project. It produces an HTML manual with prose explanations interleaved with verified Lean code excerpts pulled directly from the source files.

## Prerequisites

- [Lean 4](https://lean-lang.org/) (same toolchain as the root project)
- The root project must build successfully first

## Building

From the repository root, build the main project:

```bash
lake build
```

Then build the documentation:

```bash
cd docs/manual
lake build
```

This compiles the Verso document and produces the `docs` executable.

## Generating HTML

After building, generate the HTML output:

```bash
.lake/build/bin/docs
```

The generated site is written to `_out/html-multi/`.

## Serving locally

To preview the documentation in a browser:

```bash
cd _out/html-multi
python3 -m http.server 8080
```

Then open http://localhost:8080.

## Structure

| File | Description |
|------|-------------|
| `Docs.lean` | Top-level document: title, authors, and section includes |
| `Docs/DocDH.lean` | Diffie-Hellman section |
| `Docs/DocKDF.lean` | Key Derivation Function section |
| `Docs/DocAEAD.lean` | Authenticated Encryption section |
| `Docs/DocKEM.lean` | Key Encapsulation Mechanism section |
| `Docs/DocX3DH.lean` | X3DH protocol section |

Each Doc file uses Verso's `anchor` and `anchorTerm` directives to pull code from the corresponding source file in `PQXDHLean/`. The code excerpts are delimited by `-- ANCHOR:` / `-- ANCHOR_END:` markers in the source.
