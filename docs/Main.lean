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
  extraCss := [
r#"
.hover-info {
  display: none;
  position: fixed;
  z-index: 10000;
  background: #1e1e2e;
  color: #cdd6f4;
  border: 1px solid #585b70;
  border-radius: 6px;
  padding: 8px 12px;
  font-size: 0.9em;
  font-family: monospace;
  max-width: 60em;
  max-height: 20em;
  overflow: auto;
  white-space: pre-wrap;
  word-wrap: break-word;
  box-shadow: 0 4px 16px rgba(0,0,0,0.3);
  pointer-events: none;
}

/* Lean syntax highlighting colors for Verso token classes (github-light theme) */
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}
.hl.lean .keyword.token { color: #D73A49; }
.hl.lean .var.token { color: #24292E; }
.hl.lean .const.token { color: #6F42C1; }
.hl.lean .sort.token { color: #005CC5; }
.hl.lean .literal.token { color: #005CC5; }
.hl.lean .string.token { color: #032F62; }
.hl.lean .unknown.token { color: #24292E; }
.bp_name { font-weight: bold; white-space: nowrap; }
.bp_heading_title_row_statement { display: inline-flex !important; align-items: baseline; gap: 0.35rem; white-space: nowrap; }
.hl.lean .inter-text { color: #24292E; }
"#
  ]
  extraJs := [
r#"
(function() {
  /* Hover-info tooltips */
  var tooltip = null;
  function getTooltip() {
    if (!tooltip) {
      tooltip = document.createElement('div');
      tooltip.className = 'hover-info-tooltip';
      tooltip.style.cssText = 'display:none;position:fixed;z-index:10000;background:#1e1e2e;color:#cdd6f4;border:1px solid #585b70;border-radius:6px;padding:8px 12px;font-size:0.9em;font-family:monospace;max-width:60em;max-height:20em;overflow:auto;white-space:pre-wrap;word-wrap:break-word;box-shadow:0 4px 16px rgba(0,0,0,0.3);pointer-events:none;';
      document.body.appendChild(tooltip);
    }
    return tooltip;
  }
  document.addEventListener('mouseover', function(e) {
    var target = e.target.closest('.token');
    if (!target) target = e.target.closest('span[class]');
    if (!target) return;
    var info = target.querySelector(':scope > .hover-info');
    if (!info) return;
    var text = info.textContent.trim();
    if (!text || text.length === 0) return;
    var tip = getTooltip();
    tip.innerHTML = info.innerHTML;
    tip.style.display = 'block';
    var rect = target.getBoundingClientRect();
    var tipW = tip.offsetWidth, tipH = tip.offsetHeight;
    var left = rect.left;
    var top = rect.bottom + 4;
    if (left + tipW > window.innerWidth - 10) left = window.innerWidth - tipW - 10;
    if (left < 10) left = 10;
    if (top + tipH > window.innerHeight - 10) top = rect.top - tipH - 4;
    tip.style.left = left + 'px';
    tip.style.top = top + 'px';
  });
  document.addEventListener('mouseout', function(e) {
    var target = e.target.closest('.token');
    if (!target) target = e.target.closest('span[class]');
    if (!target) return;
    var info = target.querySelector(':scope > .hover-info');
    if (!info) return;
    var tip = getTooltip();
    tip.style.display = 'none';
  });

  /* Render markdown in docstrings inside collapsed <details> panels */
  function renderDocstringsIn(root) {
    if (typeof marked === 'undefined') return;
    var els = root.querySelectorAll('pre.docstring, code.docstring');
    for (var i = 0; i < els.length; i++) {
      var d = els[i];
      if (d.dataset.rendered) continue;
      d.dataset.rendered = '1';
      var str = d.innerText;
      var html = marked.parse(str);
      var rendered = document.createElement('div');
      rendered.classList.add('docstring');
      rendered.innerHTML = html;
      d.parentNode.replaceChild(rendered, d);
    }
  }
  /* Run on all <details> toggle events (Blueprint code panels) */
  document.addEventListener('toggle', function(e) {
    if (e.target.tagName === 'DETAILS' && e.target.open) {
      renderDocstringsIn(e.target);
    }
  }, true);
  /* Also run on page load for any already-visible docstrings */
  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', function() { renderDocstringsIn(document); });
  } else {
    renderDocstringsIn(document);
  }

  /* Syntax highlighting is done server-side by scripts/highlight-lean.mjs */
})();
"#
  ]
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
