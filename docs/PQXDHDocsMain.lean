/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual
import PQXDHDocs.Contents

open Verso Doc
open Verso.Genre Manual
open Std (HashMap)

def htmlAssets : HtmlAssets where
  features := .all
  extraCss := {}
  extraJs := {}
  extraJsFiles := {}
  extraCssFiles := {}

def htmlConfig : HtmlConfig where
  toHtmlAssets := htmlAssets
  htmlDepth := 2
  extraHead : Array Output.Html := #[]

def outputConfig : OutputConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately

def config : Config where
  toHtmlConfig := htmlConfig
  toOutputConfig := outputConfig

def renderConfig : RenderConfig where
  toConfig := config

def main := manualMain (%doc PQXDHDocs.Contents) (config := renderConfig)
