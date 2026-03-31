/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import PQXDHDocs.DocDH
import PQXDHDocs.DocKDF
import PQXDHDocs.DocAEAD
import PQXDHDocs.DocKEM
import PQXDHDocs.DocX3DH
import PQXDHDocs.DocX3DHPassiveSecrecy
import PQXDHDocs.DocSecurityDefs
import PQXDHDocs.DocPQXDH

open Verso.Genre Manual

set_option doc.verso true
set_option pp.rawOnError true

#doc (Manual) "PQXDH in Lean" =>
%%%
authors := ["Christiano Braga"]
shortTitle := "PQXDH in Lean"
%%%

A Lean 4 formalization of Signal's X3DH and PQXDH key agreement protocols,
following Bhargavan et al. (USENIX Security 2024).

The formalization uses Mathlib's `Module F G` for Diffie-Hellman and
VCV-io for security game definitions (DDH, advantage bounds).

The source code is available on [GitHub](https://github.com/Beneficial-AI-Foundation/signal-shot-PQXDH/tree/X3DH_security_properties/PQXDHLean).

{include 1 PQXDHDocs.DocDH}
{include 1 PQXDHDocs.DocKDF}
{include 1 PQXDHDocs.DocAEAD}
{include 1 PQXDHDocs.DocKEM}
{include 1 PQXDHDocs.DocX3DH}
{include 1 PQXDHDocs.DocX3DHPassiveSecrecy}
{include 1 PQXDHDocs.DocSecurityDefs}
{include 1 PQXDHDocs.DocPQXDH}
