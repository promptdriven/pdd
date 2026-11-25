# Rule-to-proof traceability

Own `src/core/rule-coverage.mjs` (Layer-1 Core: imports only Layer-1 `src/core/*`, `file-owner.mjs`, `story-lint.mjs`, and Layer-0 `src/shared/*`; zero `autopilot/` imports, zero network calls, zero AI calls). Mechanically extract diff-changed explicit rule IDs from `## Domain decisions` (in `.prompt.md`) and `## Rules to check` (in Stories), match whole-word references across formal, scenario, and native tests, classify each rule as `covered`, `not_proved`, or `uncovered`, and format non-blocking warnings for `pdd lint --diff` and structured `rule_coverage` rows for `pdd prove`.

## Domain decisions

| ID | Decision | Rule |
| --- | --- | --- |
| RC-1 | Non-blocking severity | Uncovered changed rules emit `Warning: rule coverage:` advisories only; they never raise blocking lint errors, never change `pdd lint --diff` exit code `0`, and never change `pdd prove` outcome (`Proved` / `Failed` / `Not proved`). |
| RC-2 | Explicit IDs & diff scope only | Inspect only diff-changed rules inside `## Domain decisions` (`.prompt.md`) and `## Rules to check` (Stories under `user_stories/` or `pdd/stories/`, excluding `PLAN.md`/`README.md` and `fixtures/`). Ignore YAML frontmatter, Runtime interface blocks, HTML comments, and Markdown fenced code blocks (` ``` ` / `~~~`). Unchanged merge-base rules (same `id`, normalized `text`, and `not_proved_reason`, even if line numbers shift) and plain-prose bullets without an explicit rule ID produce zero extracted rules and zero warnings. |
| RC-3 | Test-only whole-word evidence | Only canonical formal (`*.formal.test.*`, `test_formal_*.py`, `*_formal_test.py`, `formal/test_*.py`, `*_formal_test.go`, `tests/*formal*.rs`), scenario JSON (`test(s)/__tests__/**/*.json` containing a `steps` array, excluding fixtures/configs), and native test code files (excluding fixtures, mocks, helpers, snapshots, docs, prompts, Stories, and production source files) count as evidence. Whole-word boundary guards reject substring spoofs (`LED-H40`, `XLED-H4`, `LED-H4a`, `R10`, `TR1`). |
| RC-4 | Explicit `Not proved:` rationale | A rule with zero test evidence classifies as `not_proved` only when it carries a substantive `Not proved: <reason>` disclosure (containing at least 2 alphanumeric characters, outside inline backticks or double quotes) either inline on the rule row/bullet, in an indented continuation/sub-bullet directly under that bullet, or in a document-level `Not proved: <ID> (<reason>)` / `Not proved: <ID> — <reason>` / `Not proved: <ID>: <reason>` line outside fences. Empty or punctuation-only `Not proved:` disclosures stay `uncovered` with `not_proved_reason: null`. |

### Explicit rule ID grammar and Markdown extraction

- **Accepted explicit rule IDs (`isExplicitRuleId`):** Strip surrounding Markdown emphasis/backticks/brackets (`**`, `__`, `*`, `` ` ``, `[...]`) and trailing `:`. Reject known encoding/standard tokens (`UTF-8`, `UTF-16`, `UTF-32`, `SHA-1`, `SHA-256`, `SHA-384`, `SHA-512`, `ISO-8601`, `RFC-*`, `TLS-*`, `ECMA-*`). Accept uppercase tokens matching one of:
  1. Hyphenated ID: `^[A-Z]{1,12}(?:-[A-Z0-9]{1,8})+$` where at least one segment after the first `-` contains a digit or is a single uppercase letter (accepts `LED-H1`, `TR-C1`, `LED-M`, `TR-M`, `RC-1`, `RULE-01`; rejects prose words like `NON-EMPTY`, `READ-ONLY`, `FAIL-CLOSED`).
  2. Underscored ID with digit: `^[A-Z]{1,10}(?:_[A-Z0-9]{1,8})+$` containing at least one digit (accepts `LED_H1`, `TR_C1`, `R_01`; rejects `SCREAMING_SNAKE_CASE` constants like `PDD_SKILL_NAMES`).
  3. Compact alphanumeric ID: `^[A-Z]{1,6}\d{1,5}$` (accepts `R1`, `R01`, `C1`, `H2`, `INV1`, `AC1`).
- **Markdown tables:** Inside the target `## ` section (including nested `###` subsections until the next `# ` or `## ` heading), identify tables by a header row followed by a separator row. Select the ID column from the first header matching `rule id`, `id`, `code`, `ref`, or `key` (case-insensitive), else `rule`, else column `0`. Extract a row when its ID cell either matches `isExplicitRuleId` directly or begins with an explicit ID prefix (`**ID:** ...`, `` `ID` — ... ``, `[ID] ...`, `ID: ...`). Check all cells in the row for `Not proved: <reason>`.
- **ID-prefixed bullets:** Match list items (`-`, `*`, `+`, or `1.`) beginning with bold `**ID:**` / `**ID**:` / `**ID** —` / `**ID** -`, backtick `` `ID`: `` / `` `ID` — `` / `` `ID` - ``, bracketed `[ID]`, or plain `ID:` / `ID —` / `ID -` where `ID` passes `isExplicitRuleId`. Attach strictly more-indented continuation lines and sub-bullets belonging to that bullet for normalized `text` and `Not proved:` extraction.
- **Deduplication & ordering:** Deduplicate rules by `id` per file (preserving first line; keeping a substantive `not_proved_reason` if a later mention supplies one). Sort diff-changed rules by `(source, line, id)` ascending.

### Evidence matching and classification

- **Whole-word matching:** For IDs containing `-` or `_`, match `(?<![A-Za-z0-9])<segments joined by [-_]>(?![A-Za-z0-9])` case-insensitively so Python `def test_led_h1_...` and scenario `"id": "led-h1-..."` trace to `LED-H1`. For separator-less IDs (`R1`, `C1`), match `(?<![A-Za-z0-9])<id>(?![A-Za-z0-9])` case-sensitively so local variables (`const r1 = ...`) never spoof coverage.
- **Scenario JSON scanning:** Parse JSON safely; require a plain object with a `steps` array. Scan traceable metadata strings (`description`, `name`, `title`, `rules`, `rule_ids`, `criteria[].id/text/rule_id/description`, and per-step `id`, `step_id`, `name`, `description`, `rule_id`, `rule_ids`, `rules`, `tags`, `checks` object keys, and check object `criterion_id`/`rule_id`/`description`/`note`/`label`). Resolve the 1-based line number from raw JSON text.
- **Classification & sorting:** Record at most one evidence entry `{path, line, kind}` (first matching line) per `(ruleId, testFile)`. Sort `evidence` by kind (`formal`, `scenario`, `native`), then `path`, then `line`. Set `tiers` to the canonical subset of `["formal", "scenario", "native"]` present in `evidence`. Set `status` to `"covered"` when `evidence.length > 0`, else `"not_proved"` when `not_proved_reason` is non-null, else `"uncovered"`.

## Public contract

- `isExplicitRuleId(token)` → `boolean`.
- `classifyTestFileKind(filePath)` → `"formal" | "scenario" | "native" | null`.
- `extractRulesFromMarkdown(markdown, {sourcePath, fileKind})` → array of `{id: string, source: string, line: number, section: "Domain decisions" | "Rules to check", text: string, not_proved_reason: string | null}`.
- `diffChangedRules(changedDocs)` → array of changed rule entries from `{path: string, fileKind?: "prompt" | "story", before?: string, after?: string}[]`.
- `findRuleReferencesInFiles(ruleIds, testFiles)` → map from rule `id` to sorted `{path: string, line: number, kind: "formal" | "scenario" | "native"}[]` over `{path: string, kind?: "formal" | "scenario" | "native", content: string}[]`.
- `evaluateRuleCoverage({changedDocs, testFiles})` → `{rules, summary: {total: number, covered: number, not_proved: number, uncovered: number}, warnings: string[]}` where each row in `rules` is `{id, source, line, section, text, status: "covered" | "not_proved" | "uncovered", tiers: ("formal" | "scenario" | "native")[], evidence: {path: string, line: number, kind: "formal" | "scenario" | "native"}[], not_proved_reason: string | null}`.
- `formatRuleCoverageWarnings(rules)` → array of 4-part `Warning: rule coverage: <source>:<line> [rule-coverage-uncovered] ... Fix: ... Rerun: \`pdd lint --diff\`.` strings for `uncovered` rows only.
- `formatRuleCoverageSummary(result)` → `""` when `rules` is empty, else `"Rule coverage: <traced>/<total> traced (<covered> covered, <not_proved> not proved, <uncovered> uncovered[: <ids>])"`.
- `analyzeRepoRuleCoverage({root, baseRef, baseSha, changedEntries, allFiles, filterPaths})` → repo-backed wrapper resolving merge-base diffs, short-circuiting with zero test reads when zero explicit rules changed, reading canonical non-symlink test files safely, and returning `evaluateRuleCoverage(...)`.

## Dependencies

None. Pure core operations run strictly over supplied strings and records with zero I/O; the repo adapter reuses Layer-1 `FORMAL_TEST_FILE_RE`, `isTestOwnedPath`, `isLintableStoryPath`, safe in-root reads, and Layer-0 Git file listing.
