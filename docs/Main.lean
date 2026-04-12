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

/* Proof source card — no purple left border */
.proof-source-card {
  margin: 0.8rem 0;
  border: none;
  border-left: none;
  background: transparent;
  overflow: hidden;
}
.proof-source-card.bp_code_panel {
  border-left: none !important;
}
.proof-source-code {
  margin: 0;
  padding: 0.8rem 1rem;
  font-family: monospace;
  font-size: 0.88em;
  line-height: 1.6;
  white-space: pre;
  overflow-x: auto;
  color: #24292E;
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

  /* Transform proof source blocks: card styling + syntax highlighting */
  onReady(function() {
    var markerText = '-- PROOF-SOURCE';
    document.querySelectorAll('pre').forEach(function(el) {
      var text = el.textContent || '';
      if (text.trimStart().indexOf(markerText) !== 0) return;
      /* Remove marker line */
      var idx = text.indexOf(markerText);
      var rest = text.substring(idx + markerText.length);
      var nlIdx = rest.indexOf('\n');
      var code = nlIdx >= 0 ? rest.substring(nlIdx + 1) : rest;
      var keywords = /\b(by|cases|simp|exact|subst|rw|rewrite|apply|intro|intros|have|show|suffices|induction|constructor|refine|calc|ring|omega|norm_num|linarith|aesop|trivial|contradiction|exfalso|congr|ext|funext|sorry|with|match|fun|let|do|if|then|else|for|in|return|pure|try|catch|throw|unless|where|only|guard|logInfo|throwError)\b/g;
      var consts = /\b(none|some|true|false)\b/g;
      /* Escape HTML */
      var html = code.replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');
      /* Highlight */
      html = html.replace(/(--[^\n]*)/g, '<span style="color:#6A737D">$1</span>');
      html = html.replace(keywords, '<span style="color:#D73A49">$1</span>');
      html = html.replace(consts, '<span style="color:#005CC5">$1</span>');
      html = html.replace(/(\|) /g, '<span style="color:#D73A49">$1</span> ');
      /* Find the nearest theorem/definition (not proof) for context */
      var prev = el.previousElementSibling;
      var theoremLabel = '';
      while (prev) {
        if (prev.classList && (prev.classList.contains('bp_kind_theorem_wrapper') ||
            prev.classList.contains('bp_kind_definition_wrapper') ||
            prev.classList.contains('bp_kind_lemma_wrapper'))) {
          var cap = prev.querySelector('.bp_caption');
          var lab = prev.querySelector('.bp_label');
          if (cap && lab) theoremLabel = cap.textContent.trim() + ' ' + lab.textContent.trim();
          break;
        }
        /* Also check inside proof wrappers for a preceding theorem */
        if (prev.classList && prev.classList.contains('bp_kind_proof_wrapper')) {
          prev = prev.previousElementSibling;
          continue;
        }
        /* Check code panel wrappers */
        if (prev.classList && prev.classList.contains('bp_code_panel_wrapper')) {
          prev = prev.previousElementSibling;
          continue;
        }
        prev = prev.previousElementSibling;
      }
      var title = theoremLabel ? 'Proof for ' + theoremLabel : 'Proof';
      /* Wrap in foldable card like blueprint code blocks */
      var wrapper = document.createElement('div');
      wrapper.className = 'bp_wrapper bp_code_panel_wrapper';
      var details = document.createElement('details');
      details.className = 'bp_code_block bp_code_panel proof-source-card';
      details.setAttribute('open', '');
      var summary = document.createElement('summary');
      summary.className = 'bp_heading lemma_thmheading';
      summary.innerHTML = '<span class="bp_caption lemma_thmcaption bp_code_summary_text">Code for ' + title + '</span>';
      var pre = document.createElement('pre');
      pre.className = 'proof-source-code';
      pre.innerHTML = html;
      details.appendChild(summary);
      details.appendChild(pre);
      wrapper.appendChild(details);
      el.parentNode.replaceChild(wrapper, el);
    });
  });

  /* Make proof blocks foldable and rename to "Proof for Theorem X.Y" */
  onReady(function() {
    document.querySelectorAll('.bp_kind_proof_wrapper').forEach(function(proofEl) {
      /* Find preceding theorem */
      var prev = proofEl.previousElementSibling;
      var theoremLabel = '';
      while (prev) {
        if (prev.classList && (prev.classList.contains('bp_kind_theorem_wrapper') ||
            prev.classList.contains('bp_kind_definition_wrapper') ||
            prev.classList.contains('bp_kind_lemma_wrapper'))) {
          var cap = prev.querySelector('.bp_caption');
          var lab = prev.querySelector('.bp_label');
          if (cap && lab) theoremLabel = cap.textContent.trim() + ' ' + lab.textContent.trim();
          break;
        }
        if (prev.classList && (prev.classList.contains('bp_kind_proof_wrapper') ||
            prev.classList.contains('bp_code_panel_wrapper'))) {
          prev = prev.previousElementSibling;
          continue;
        }
        prev = prev.previousElementSibling;
      }
      var title = theoremLabel ? 'Proof for ' + theoremLabel : 'Proof';
      /* Wrap in foldable details */
      var heading = proofEl.querySelector('.bp_kind_proof_heading');
      var content = proofEl.querySelector('.bp_kind_proof_content');
      if (heading && content) {
        var details = document.createElement('details');
        details.className = 'bp_code_block';
        details.setAttribute('open', '');
        var summary = document.createElement('summary');
        summary.className = 'bp_heading lemma_thmheading';
        summary.innerHTML = '<span class="bp_caption lemma_thmcaption">' + title + '</span>';
        details.appendChild(summary);
        details.appendChild(content.cloneNode(true));
        proofEl.innerHTML = '';
        proofEl.appendChild(details);
      }
    });
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
