import VersoManual
import VersoBlueprint
import PQXDHDocs.Contents

open Verso.Genre Manual
open Informal

def bpCss : CSS := CSS.mk
r#"
/* Lean syntax highlighting colors (github-light theme) */
:root {
  --verso-code-keyword-color: #D73A49;
  --verso-code-keyword-weight: normal;
}
.hl.lean .keyword { color: #D73A49; }
.hl.lean .var { color: #24292E; }
.hl.lean .const { color: #6F42C1; }
.hl.lean .sort { color: #005CC5; }
.hl.lean .literal { color: #005CC5; }
.hl.lean .string { color: #032F62; }
.hl.lean .unknown { color: #24292E; }
.hl.lean .inter-text { color: #24292E; }

/* Rendered docstrings inside code blocks */
.bp_external_decl_body .docstring {
  font-family: var(--verso-text-font-family, sans-serif);
  font-size: 0.95em;
  line-height: 1.5;
  white-space: normal;
  padding: 0.6rem 0.8rem;
  margin: 0.4rem 0 0 0;
  background: #f8fafc;
  border-left: 3px solid #6F42C1;
  border-radius: 0 4px 4px 0;
}
.bp_external_decl_body .docstring code {
  background: #eef2f7;
  padding: 0.1em 0.3em;
  border-radius: 3px;
  font-size: 0.9em;
}
.bp_external_decl_body .docstring p {
  margin: 0.3em 0;
}

/* Show code bodies by default (open collapsed details) */
details.bp_code_block[open] > summary {
  margin-bottom: 0.5rem;
}

/* Blueprint heading: "Definition 1.1 (name)" pattern */
.bp_name {
  font-weight: bold;
  font-style: italic;
  white-space: nowrap;
}
.bp_heading_title_row_statement {
  display: inline-flex !important;
  align-items: baseline;
  gap: 0.35rem;
  white-space: nowrap;
}
"#

def bpJs : JS := JS.mk
r#"
(function() {
  function onReady(fn) {
    if (document.readyState === 'loading') {
      document.addEventListener('DOMContentLoaded', fn);
    } else {
      fn();
    }
  }

  /* Insert blueprint label names: "Definition 1.1" -> "Definition 1.1 (dh_spec)" */
  onReady(function() {
    document.querySelectorAll('.bp_heading_title_row_statement').forEach(function(row) {
      if (row.querySelector('.bp_name')) return;
      var caption = row.querySelector('.bp_caption[title]');
      if (!caption) return;
      var name = caption.getAttribute('title');
      if (!name || name.length === 0) return;
      var nameSpan = document.createElement('span');
      nameSpan.className = 'bp_name';
      nameSpan.textContent = '(' + name + ')';
      row.appendChild(nameSpan);
    });
  });

  /* Open all code blocks and render docstrings as markdown */
  onReady(function() {
    /* Open code blocks first */
    document.querySelectorAll('details.bp_code_block').forEach(function(d) {
      d.setAttribute('open', '');
    });

    /* Render markdown in docstrings (re-run after opening details) */
    if (typeof marked !== 'undefined') {
      document.querySelectorAll('pre.docstring, code.docstring').forEach(function(el) {
        if (el.dataset.rendered) return;
        /* Skip docstrings inside hover-info (those are Mathlib tooltips) */
        if (el.closest('.hover-info')) return;
        el.dataset.rendered = '1';
        var text = el.innerText;
        if (!text || !text.trim()) return;
        var html = marked.parse(text);
        var rendered = document.createElement('div');
        rendered.className = 'docstring';
        rendered.innerHTML = html;
        el.parentNode.replaceChild(rendered, el);
      });
    }
  });

  /* Set modern style by default */
  onReady(function() {
    document.documentElement.setAttribute('data-bp-style', 'modern');
  });

  /* Suppress empty Tippy tooltips */
  onReady(function() {
    document.querySelectorAll('.hover-info').forEach(function(el) {
      var text = el.textContent.trim();
      if (!text) el.remove();
    });
  });
})();
"#

def main (args : List String) : IO UInt32 :=
  PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc PQXDHDocs.Contents)
    args
    (extensionImpls := by exact extension_impls%)
    (config := {
      toHtmlAssets := {
        extraCss := .ofList [bpCss]
        extraJs := .ofList [bpJs]
      }
    })
