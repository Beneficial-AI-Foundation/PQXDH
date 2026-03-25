#!/usr/bin/env node
/**
 * Post-process Blueprint HTML files to add Shiki Lean syntax highlighting
 * to bare <pre> blocks inside proof sections and structure code blocks.
 */
import { createHighlighterCoreSync } from 'shiki/core'
import { createJavaScriptRegexEngine } from 'shiki/engine/javascript'
import lean from 'shiki/langs/lean.mjs'
import githubLight from 'shiki/themes/github-light.mjs'
import { readFileSync, writeFileSync } from 'fs'
import { execSync } from 'child_process'

const highlighter = createHighlighterCoreSync({
  themes: [githubLight],
  langs: [lean],
  engine: createJavaScriptRegexEngine(),
})

/**
 * Highlight Lean code. For tactic-only snippets (no top-level declaration),
 * wrap in a dummy theorem so the grammar tokenizes tactics properly,
 * then extract the tactic lines.
 */
function highlightLean(code) {
  const trimmed = code.trim()
  const isTopLevel = /^\s*(theorem|def|lemma|structure|class|instance|inductive|noncomputable|opaque|axiom|import|variable|open|section|namespace|set_option|abbrev)/.test(trimmed)

  let html = highlighter.codeToHtml(trimmed, { lang: 'lean', theme: 'github-light' })

  // Post-process: add tactic keyword highlighting
  // The Lean TextMate grammar doesn't tokenize tactic names, so we do it manually.
  const tactics = 'simp|only|exact|subst|rw|rewrite|apply|intro|intros|have|show|suffices|cases|induction|constructor|refine|calc|ring|omega|norm_num|linarith|aesop|trivial|contradiction|exfalso|congr|ext|funext|sorry'
  const tacticRe = new RegExp(`(?<=>|^|\\s)(${tactics})(?=\\s|\\[|$|<)`, 'g')
  html = html.replace(tacticRe, (m, tac) => {
    // Only colorize if not already inside a colored span
    return `<span style="color:#D73A49">${tac}</span>`
  })

  // Also highlight Lean identifiers used as lemma names after tactics
  const lemmaStyle = 'color:#6F42C1'
  html = html.replace(
    /(<span style="color:#D73A49">(?:simp|rw|exact|apply|have)<\/span>\s+(?:only\s+)?)(\[?)([A-Za-z_][A-Za-z0-9_.']*)/g,
    (m, pre, bracket, name) => `${pre}${bracket}<span style="${lemmaStyle}">${name}</span>`
  )

  return html
}

const outputDir = process.argv[2] || '_out/blueprint'

const files = execSync(`find ${outputDir} -name '*.html'`, { encoding: 'utf8' })
  .trim().split('\n').filter(Boolean)

let totalHighlighted = 0

for (const file of files) {
  let html = readFileSync(file, 'utf8')
  let changed = false

  // Match bare <pre> inside proof_content divs
  html = html.replace(
    /(<div class="bp_content proof_content">[\s\S]*?)<pre>([\s\S]*?)<\/pre>/g,
    (match, before, code) => {
      if (code.includes('class="hl"') || code.includes('class="shiki"')) return match
      const trimmed = code.trim()
      if (!trimmed) return match
      try {
        const highlighted = highlightLean(trimmed)
        changed = true
        totalHighlighted++
        return before + highlighted
      } catch (e) {
        return match
      }
    }
  )

  // Also highlight standalone <pre> blocks (structure definitions etc.)
  html = html.replace(
    /(<\/p>\s*)<pre>((?:(?!class=)[^<]|<(?!\/pre))*)<\/pre>/g,
    (match, before, code) => {
      const trimmed = code.trim()
      if (!trimmed) return match
      if (!trimmed.match(/\b(structure|def|theorem|lemma|simp|exact|subst|sorry|where|import|variable|noncomputable|inductive|opaque)\b/))
        return match
      try {
        const highlighted = highlightLean(trimmed)
        changed = true
        totalHighlighted++
        return before + highlighted
      } catch (e) {
        return match
      }
    }
  )

  // Inject label names into definition/theorem/lemma headings.
  // Blueprint stores the name in title="..." but only renders "Definition 1.".
  // The CSS ::after on thmlabel already adds a dot, so we don't add another.
  // We transform it to "Definition 1. (MessageSecrecy)" etc.
  html = html.replace(
    /(<span class="bp_caption [^"]*" title="([^"]+)">[^<]*<\/span><span class="bp_label [^"]*">)(\d+)(<\/span>)/g,
    (match, pre, name, num, post) => {
      changed = true
      const displayName = name.replace(/[«»]/g, '')
      return `${pre}${num}${post} <span class="bp_name">(${displayName})</span>`
    }
  )

  if (changed) {
    writeFileSync(file, html)
  }
}

console.log(`[highlight-lean] Highlighted ${totalHighlighted} code blocks across ${files.length} files.`)
