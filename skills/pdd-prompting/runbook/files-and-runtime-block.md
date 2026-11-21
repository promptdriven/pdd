# Runbook: Files, Schemas, Expected Values, and Approvals

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 1. What the PDD interpreter is

The PDD interpreter runs `*.prompt.md` files directly as programs (requires `gh auth status`). Checks upload Git-visible selected files (max `10 MiB`, `10,000` files); inspect selection offline with `pdd test --files`. Never commit secrets. Interactive single-file UIs run directly with `pdd simulate prompts/<app>.prompt.md` (zero `app-map.json`, Story, or test file needed); Story-driven workflow order is: Story → prompt → test → `pdd test` → offer `pdd simulate <story>` → approval → PR 1 → code.

## 2. The files

- **`prompts/<job>.prompt.md`**: plain Markdown—no embedded `Runtime interface` JSON block is required for `pdd test`, `app-map.json`, or Hybrid simulation (any embedded block is stripped from LLM context). **One rule, one prompt.** A command-line program has one program prompt (section 6). Never own test files (`test/**`, `tests/**`, `*.test.*`). Keep prose `<= 500` lines. For pure OS/net/DB plumbing with no user-facing policy (§21), add YAML frontmatter `kind: native-only` and `reason: <native effect>`.
- **`user_stories/<story>.md`**: one `"As a …, I want …, so that …"` line plus numbered `## Acceptance criteria` starting at `1.`, straight quotes (`"`), real values. Do not name code ("`splitBill(2, 4)` returns …"): the person must read and approve it. Optional scope narrowing uses one fenced `pdd-boundary` block listing repo-relative prompt paths.
- **`tests/<story>.json`**: native Short JSON is accepted directly by `pdd test`, `pdd lint`, `pdd simulate`, and code-space replay (omit `schema_version`, `story_path`, and `criteria` to auto-bind Story lines). Matched by basename inside any `tests` or `test` folder. If the repo's own tests are in `tests/` or `test/`, use `tests/runtime/` or `test/runtime/`. Add `<story>.<world>.json` only for a different starting world. Keep steps small (`<= 10` moves/rows/calls, 10-minute server cap, `<= 15` steps / `1,000` lines).
- **Shared contracts, seeds & extra source**: link `contracts/*.md` under `## Dependencies` or reference `{"$contract": "contracts/records.json#/defs/order"}` in explicit schemas; reuse worlds with `"initial_world": {"$seed": "contracts/seed.json", "set": {"/orders": []}}`. Extra repo-relative text files: scenario `"context": [{"prompt_path": "...", "paths": [...]}]` (`<= 16` files, `120 KiB`, never the Story/test/answers) or root `pdd-source.json` (`{"include": [...]}`).
- **Approvals (`--said`)**:
  - Show the gate (in a normal workflow run, show pdd's Story card as printed). Judge the person's later reply in any chat. A question, change request or earlier message is not approval. No exact phrase is needed. Never invent a decision or edit approval fields. See [Record a chat approval](https://github.com/promptdriven/pdd/blob/main/docs/cli.md#record-a-chat-approval).
  - Record exact words with `pdd workflow approve N --said - <<'PDD_SAID'` (or `pdd approve PROMPT --said - <<'PDD_SAID'`). Choose a delimiter absent as a whole line from the payload; keep it quoted; `--said -` records stdin exactly, including newlines. Blank input is refused; pdd does not grade nonblank words.
  - A prompt edit invalidates the gate unless a normal run's prompt-only repair passes `pdd test` in full (`automatic-check-pass` opens PR 1 via `workflow done`). Without `--said`, a person at a normal terminal answers y/N once; for a caller outside a normal terminal, `pdd workflow approve` tells the agent to ask the person, then run with --said and their words. Native Herdr area-chat evidence never authorizes approval. Only an explicit approve call advances an approval gate. Warn when a workflow has no approve gate before code.
  - Root `pdd.json` (`sourceRoot` for workflow runs, Git root for standalone `pdd approve`) with `"strict_approvals": true` permits only a person terminal and refuses `--said`.
- **Merges**: pdd never merges. An agent may merge only on the person's explicit chat request. Resolve exact head and require at least one check and all required checks green. First post a PR comment starting `Merge requested by the person: "…"` using a body file (never shell-interpolating untrusted words). A failed comment stops. Recheck head/checks, then run `gh pr merge PR --merge --match-head-commit <head>`. A changed head stops.

## 3. Schema rules

**Lazy-interface prose (`## Input` / `## Output` / `## Ports`):** never write bare untyped `object` fields (e.g. `value is null or object`, `"returns the snapshot object"`)—lazy synthesis generates strict closed schemas that fail at runtime with `result-schema-incompatible`. Enumerate concrete properties + types for every object (or explicitly state `"open object"` when arbitrary keys are intended), and avoid polymorphic write-port payloads (split distinct payload shapes into separate `<port>.<op>` operations or a tagged envelope).

Applies to explicit `$contract` schemas and explicit `app-map.json` `state_schema` (compact `app-map.json` may omit `state_schema` so it is synthesized from `initial_state`):
1. Top level is `"type": "object"` with `properties`, `required` (subset of `properties`, unique), and `"additionalProperties": false`.
2. `type` is one string (`object`, `array`, `string`, `integer`, `number`, `boolean`, `null`), never a list like `["string", "null"]`. Nullable uses `{"oneOf": [{"type": "string"}, {"type": "null"}]}` (omit optional fields from `required` instead of `oneOf` where possible).
3. Arrays require `items`. Allowed keywords only: string (`minLength`, `maxLength`, `pattern`), number/integer (`minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`, integer bounds within `±(2^53-1)`), array (`items`, `minItems`, `maxItems`, `uniqueItems`), object (`properties`, `required`, `additionalProperties`, `minProperties`, `maxProperties`), shared (`enum`, `const`, `title`, `description`, `default`, `examples`, `format`). `$ref`, `$defs`, `anyOf`, `if` are refused.
4. Whole numbers outside `±(2^53-1)` for JS Number inputs use exact exponential spelling (`n.toExponential()`); keep BigInt-only integers in plain digits (verified in §17 native vectors).

## 4. Expected values

- Expected values come from the Story and the person—never from observed code or simulation output, and never edited to force a pass. If ambiguous, ask the person.
- Acknowledge intentional nearby-number lint advisories in root `pdd-numeric-reviews.json` (`schema_version: "pdd.numeric-reviews.v1"`, matching `test_sha256`, `step_id`, `criterion_id`, `target`, `path`, `value`, and one-line `reason`; `<= 100` entries / `16 KiB`).
