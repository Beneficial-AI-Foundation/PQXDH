/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual
import VersoBlueprint

import PQXDHDocs.DocDH
import PQXDHDocs.DocKDF
import PQXDHDocs.DocAEAD
import PQXDHDocs.DocKEM
import PQXDHDocs.DocX3DH
import PQXDHDocs.DocSecurityDefs
import PQXDHDocs.DocPQXDH

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Informal

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "PQXDH in Lean" =>
%%%
authors := ["Christiano Braga"]
shortTitle := "PQXDH in Lean"
%%%

The PQXDH (Post-Quantum Extended Diffie-Hellman) protocol is an extension of X3DH that adds post-quantum
resistance via a Key Encapsulation Mechanism (KEM). This formalization covers both the X3DH classical
core and the full PQXDH protocol with its post-quantum KEM layer, following the description in
[Bhargavan et al.](https://www.usenix.org/system/files/usenixsecurity24-bhargavan.pdf) (USENIX Security 2024).

The formalization includes:
- Abstract algebraic definitions for the cryptographic primitives (DH, KDF, AEAD, KEM).
- The X3DH protocol with its functional correctness and handshake theorems.
- The full PQXDH protocol extending X3DH with a KEM component.
- Security definitions: adversary models, hardness assumptions, and protocol properties.
- The main security theorems (Theorems 1–3, 5–6) from the paper, stated with their
  cryptographic hypotheses.

The source code is available on [GitHub](https://github.com/Beneficial-AI-Foundation/signal-shot-PQXDH/tree/christiano/pqxdh).

{include 1 PQXDHDocs.DocDH}
{include 1 PQXDHDocs.DocKDF}
{include 1 PQXDHDocs.DocAEAD}
{include 1 PQXDHDocs.DocKEM}
{include 1 PQXDHDocs.DocX3DH}
{include 1 PQXDHDocs.DocSecurityDefs}
{include 1 PQXDHDocs.DocPQXDH}

{blueprint_graph}

{bp_summary}
