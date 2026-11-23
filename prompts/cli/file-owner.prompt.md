# File owner lookup

Own `src/file-owner.mjs`. Answer which `.prompt.md` owns a repository file using local Git-visible files only (zero network, auth, or interpreter calls).

## Domain decisions

- **Honest ownership (`binding` and `header` only):**
  - Only explicit entries in Git-visible `pdd-bindings.json` (`pdd.bindings.v1`) and top-of-file ownership headers (`header`) confer ownership (`owner`, `owners`, `source`).
  - Opening-sentence prose mentions (`promptClaims`) and mirrored path/stem matches are **advisory hints only**: they never populate `owner` or `owners`, never set `certain: false`, and emit a `note` advising `add a // Prompt: header or a pdd-bindings.json entry`.
  - `owners` lists deduplicated `binding` prompts first, then `header` prompts in line order. `owner` is `owners[0] ?? null`. `source` is `'binding'` or `'header'` when owned (or `'binding'` for a prompt-less binding entry), else `null`.
  - `certain` is `false` only when a binding or header names a prompt not in Git-visible files, when `pdd-bindings.json` is unreadable/malformed/oversized (`> 64 KiB`), or when an un-bound file head cannot be read.
- **Top-of-file (first 4 KiB) header parser (<a id="generated-from-header"></a>`Generated from` / `Prompt:` headers):**
  - Inspect complete lines inside the first `4,096` UTF-8 bytes (drop a cut final line when file size exceeds `4,096`; skip lines `> 1,100` chars).
  - Skip Markdown fenced code blocks while tracking exact opening delimiter character (`` ` `` or `~`) and length (`>= 3`) so an outer four-backtick fence containing a nested three-backtick example never closes early and documentation examples never claim file ownership.
  - Recognize `Prompt: <path>.prompt.md` and legacy `Generated from <path>.prompt.md` inside comment forms (`//`, `#`, `--`, `;`, `/* ... */`, `*`, `<!-- ... -->`, `{/* ... */}`, `"""..."""`, `'''...'''`, plus optional legacy `(sha256: HEX)` or `sha256=HEX` suffix), as well as YAML frontmatter `prompt: <path>.prompt.md` inside a leading `---` block, using linear-time non-backtracking matching.
  - Drop non-canonical paths (absolute, backslashes, control chars, `.`, `..`, empty, or `.git` segments).
- **Single-scan repository loader & 3 correctness invariants:**
  - Share one `loadOwnerContext` loader across `findOwners`, `findTestPromptViolations`, and `runOwner` so `gitFiles`, `pdd-bindings.json`, and `*.prompt.md` are scanned once.
  - Enforce consistent Git-visibility checks for `pdd-bindings.json` and read `65,537` bytes (`64 KiB + 1`) so oversized bindings files fail closed as unreadable (`false`) instead of silently truncating.
  - Never suppress ordinary misplaced-owner diagnostics on a test file when that test file also carries a `isTestPromptPath` owner (mixed-owner bug fix).
  - `findTestPromptViolations` reports blocking `test-file-claim` errors strictly for explicit `binding` / `header` test ownership (never from prose mentions); `runOwner` may emit non-blocking stderr warnings for prose test mentions with exit `0`.
- **Pure hash helpers retained for compatibility:** export `promptHeaderHash`, `headerHashState`, `moduleContentHash`, `updateHeaderHash`, and `promptClaims`.

## Public contract

- `headerEntries(content)`, `headerPrompts(content)`, `promptHeaderHash(content)`, `headerHashState(hash, promptContent)`, `moduleContentHash(content)`, `updateHeaderHash(codeText, promptPath, hash)`, `promptClaims(promptPath, content)`
- `isTestOwnedPath(path)`, `isTestPromptPath(path)`
- `resolveOwners({ paths, allPaths, bindings, heads, prompts }) -> { schema_version: 'pdd.owner.v1', files }`
- `findOwners({ root, paths }, ports)`
- `findTestPromptViolations({ root, promptPaths, checkPaths }, ports) -> { ok, violations }`
- `runOwner({ cwd, paths, json }, ports) -> exitCode`

## Dependencies

- Read the full [Prompting guide](../../skills/pdd/references/prompting.md) before changing this prompt.
- Layer-0 `src/shared/git-context.mjs` (`gitFiles`) and `src/shared/workspace-policy.mjs` (`interfaceBlocks`).
