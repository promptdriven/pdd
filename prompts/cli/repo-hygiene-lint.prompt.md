# Repo hygiene and offline PDD lint

Own `src/repo-hygiene-lint.mjs` (thin facade) and `src/core/lint/*.mjs`. Run 100% offline, deterministic, PDD-files-only lint with zero AI calls, zero network calls, zero batch-state writes, zero `autopilot/` imports, and zero `runtime-seam` imports.

## Domain decisions

- **Strict Layer-1 DAG:** `src/core/lint/*.mjs` imports only peer `src/core/lint/*`, Layer-1 core helpers (`file-owner`, `story-lint`, `product-documents`, `svg-layout`), and Layer-0 `src/shared/*`. Test-code sleep and skip checks live in Layer-2 `src/autopilot/lint-sleep-skip.mjs`.
- **Workspace scope and safety:** Resolve `realRoot = realpathSync(root)`, list Git-visible paths once via `gitFiles(realRoot)` unless `files` is supplied, resolve `workspacePolicy` from `workspacePolicy` / `workspaceRoot` / `realRoot`, exclude secret paths (`isSecretPath`) and paths outside `workspace.allows`, and skip `fixtures/` unless explicitly selected. Open regular in-root files with `O_NOFOLLOW | O_NONBLOCK` and verify `dev`/`ino` parity without throwing on unreadable, escaping, symlinked, binary, or oversized files.
- **Single-pass I/O:** Read only the 4 KiB header window of eligible production code files to check `broken-prompt-header` and resolve prompt ownership; read full code file text lazily only for prompt-owned files or files matched by explicit custom rules.
- **4-part agent-teaching diagnostics:** Every `'error'` finding — and every `'warn'` finding that supplies a fix hint — includes location (`path:line [code]`), invariant violated, a concrete 1-line `Fix:`, and a `Rerun:` command (default `pdd lint`).
- **Offline CLI handler (`runLocalLint`):** Runs `lintRepoProject`, optional `.ui.svg` layout checks (`svg-layout`), optional `--diff [BASE]` spotlight (`test-inventory`), and optional base-trusted `lint.commands` loaded strictly from `git show <baseSha>:pdd.json` (skipping untrusted working-tree command edits unless `--trust-working-tree` is explicitly requested). Clean repositories print `Local lint: 0 errors, 0 warnings. (0 AI/network calls)` to `stdout` with empty `stderr` and exit `0`; errors print to `stderr` and exit `1`. `--json` emits `{schema_version: 'pdd.local-lint.v1', ok, exit_code, local_only: true, summary_line, problems, warnings, findings, diff?, commands?}`.

## Built-in deterministic rules

| Rule IDs | Default | Target | Invariant |
| --- | --- | --- | --- |
| `lint-config-invalid` | `error` | `pdd.json`, `rules/lint/*.json` | Valid JSON, schema, safe regexes, bounded globs, <= 100 custom rules, <= 16 lint commands. |
| `broken-prompt-header` | `error` | Production code headers | Every `// Prompt: <path>` or `// Generated from <path>` header points to an existing Git-visible `.prompt.md` file (path-only; ignores sha256 staleness). |
| `broken-dependency-link` | `error` | Prompt `## Dependencies` | Every relative Markdown link resolves to an existing Git-visible file or directory. |
| `native-only-unknown-port` | `error` | `kind: native-only` Prompt (frontmatter or Runtime interface JSON) + checkable deps/contracts | Every `<port>.<op>` wired via YAML `ports: [...]` (inline, indented, or YAML 1.2 zero-indented block list), canonical `## Ports` / explicit port columns (checked before exclusion keywords, supporting return-type signatures and post-delimiter backticks, never suppressed by SQL DDL columns), explicit wiring cues, or declared-prefix prose matches a declared port or exported `<stem>.<op>` / `<dir>.<op>` peer operation on linked checkable `.prompt.md` files or `contracts/**/*.md` docs (never arbitrary `docs/*.md`). Explicit frontmatter `ports:` and `## Ports` declarations are checked even when `## Dependencies` lists no checkable prompts. |
| `story-code-internals`, `story-missing-criteria` | `error` | Story | Stories state user-observable behavior without code internals and include `## Acceptance criteria` with >= 1 item. |
| `diff-focus-only`, `diff-conflict-marker`, `diff-shadow-bin`, `misplaced-test-prompt` (in `--diff`) | `error` | `BASE..WORKTREE` diff | No executable `.only` focus markers in test files, no merge conflict markers in non-doc files, no tracked/untracked/on-disk shadow runtime binaries under `node_modules/.bin/`, and no newly added/modified misplaced test prompts. |
| `misplaced-test-prompt` (repo-wide), `lint-config-untrusted`, `prompt-dependency-cycle`, `prompt-larger-than-code` (`codeLines >= 25`), `prompt-code-fence-*`, `prompt-imperative-code`, `prompt-missing-*`, `native-only-contract-incomplete`, `story-implementation-path`, `story-raw-digest`, `story-generic-role`, `story-vague-criterion`, `story-bloated-criteria`, `story-too-long`, `story-unbound-criteria`, `product-prompt-inventory-drift`, `product-boundary-unwired`, `product-boundaries-unparseable` | `warn` | PDD files | Advisory quality and hygiene checks configurable to `"off"`, `"warn"`, or `"error"` via `pdd.json` (in `--diff` and `pdd prove`, merge-base `pdd.json` and `rules/lint/*.json` control disables/weakenings and untrusted overrides emit `lint-config-untrusted`). |

## Extensible project config and ReDoS / glob safety

`loadProjectLintConfig` loads workspace-local `rules/lint/*.json` before `pdd.json` `"lint"`:
- `disable`, `rules`, `custom_rules` (capped at 100, deduplicated by `id` so later rules override cleanly; `include`/`exclude` globs filter paths before disk reads), and `commands` (up to 16 repo-native linter commands allowed only in merge-base `pdd.json`, never in `rules/lint/*.json`).
- `loadBaseTrustedLintOverrides` reads merge-base `rules/lint/*.json` and `pdd.json` so `pdd lint --diff` and `pdd prove` ignore untrusted working-tree/branch rule disables or severity weakenings.
- `parseRegexSafe` rejects backreferences, nested quantifiers, lookarounds with unbounded quantifiers, non-literal escapes (`\x`, `\u`, `\c`, `\0`) in repeated alternations, nested overlapping alternations under enclosing quantifiers, repeated alternations under `/iu` Unicode case folding, and chained/adjacent unbounded quantifiers.
- `compileGlobMatcher` matches paths with a strictly linear DP matcher (zero regex compilation, max 12 wildcards, max 256 chars).

## Polyglot `--diff [BASE]` spotlight (`src/core/lint/test-inventory.mjs`)

- Diffs `BASE..WORKTREE` (failing closed when base comparison is unavailable; includes tracked changes plus untracked non-ignored files), excludes `helpers/`, `fixtures/`, and `mocks/` utility files, catches `.only` / `.only.each` / multiline `.only`, shadow binaries under `node_modules/.bin/`, and any leftover conflict marker line, and supports JS/TS (Prettier `semi: false`, Vitest timeouts, multi-line chained `expect()` matchers), Python (`def test_*`, `pytest.raises`, `@pytest.mark.skip*`, `@unittest.skip*`, `@pytest.mark.parametrize`), Go (`func Test*`, `t.Run`, `t.Skip*`, `t.Error*`/`t.Fatal*`), and Rust (`tests/**/*.rs`, `*_test.rs`, inline `#[cfg(test)]` modules, `#[test]`/`#[*::test]`, `#[ignore]`, `#[should_panic]`, `assert*!`/`matches!`/`panic!`, and `#[test_case(...)]`).
- Reclassifies cross-file moved tests and Git `R...` file renames separately from genuinely removed tests, flags mock-only boundary tests (`mockOnlyBoundaryTests`) when changed production I/O/subprocess boundary code is only covered by mocked tests with zero real unmocked boundary calls, and reports advisories for removed tests, moved tests, new skips, dropped assertions, dropped table-driven cases, `*.snap` edits, and test-harness / `pdd.json` / `rules/lint/*.json` / `scripts.test` / CI edits.

## Dependencies

- [Story quality lint](story-lint.prompt.md): `isLintableStoryPath` and `lintStory`.
- [File owner lookup](file-owner.prompt.md): `findTestPromptViolations`, `headerEntries`, `isTestOwnedPath`, and `resolveOwners`.
- [SVG layout lint](svg-layout.prompt.md): `lintSvgLayouts`.
- [Product plans and progress](product.prompt.md): `auditProductPlan`.
