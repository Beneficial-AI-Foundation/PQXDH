/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual

import Docs.Papers
import Docs.DocFeatures
import Docs.DocDH
import Docs.DocKDF
import Docs.DocAEAD
import Docs.DocKEM
import Docs.DocX3DH

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso. Here, they're used to have the text refer to Verso code used in the text's
-- own source.
open Verso.Genre.Manual.InlineLean

-- This gets access to tools for showing Lean code that's loaded from external modules.
open Verso.Code.External

open Docs

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../../../PQXDHLean/Examples"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "PQXDHLean.X3DH"

#doc (Manual) "X3DH in Lean" =>
%%%
authors := ["Christiano Braga"]
shortTitle := "X3DH in Lean"
%%%

The PQXDH (Post-Quantum Extended Diffie-Hellman) protocol is an extension of X3DH that adds post-quantum
resistance via a Key Encapsulation Mechanism (KEM). In the current state of this formalization we focus
on X3DH, as it is a central component of PQXDH: X3DH provides the classical Diffie-Hellman core on top
of which the post-quantum KEM layer is composed. Understanding and verifying X3DH first is therefore
a necessary stepping stone toward the full PQXDH protocol.

This is an initial specification — not a complete formalization.
We declare algebraic (dependent-typed) signatures for the main components of the protocol.
There is no attacker model, and no security properties are stated or proved.
The main purpose is to show how the protocol can be specified in a way that is close to the description
in [Bhargavan et al.](https://www.usenix.org/system/files/usenixsecurity24-bhargavan.pdf), and to show how the different components (DH, KDF, AEAD) fit together.

The source code is available on [GitHub](https://github.com/Beneficial-AI-Foundation/signal-shot-PQXDH/tree/christiano/pqxdh).

{include 1 Docs.DocDH}
{include 1 Docs.DocKDF}
{include 1 Docs.DocAEAD}
{include 1 Docs.DocKEM}
{include 1 Docs.DocX3DH}
