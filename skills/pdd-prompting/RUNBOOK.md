# PDD interpreter runbook

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

## How to use this runbook

Read this index first, then open **only the 1–2 topic files** under `runbook/`
(in the `pdd-prompting` skill folder; `skills/pdd-prompting/runbook/` in the
installed `pdd` package) that match your current task or section `§N`.
Do not read unrelated topic files.

| Topic file | Sections | Open this file when… |
|---|---|---|
| `runbook/files-and-runtime-block.md` | §1–§4 | Writing or editing `prompts/<job>.prompt.md`, a `Runtime interface` block, `user_stories/<story>.md`, `tests/<story>.json`, strict JSON Schemas, expected values, or recording chat approvals / requested merges |
| `runbook/checks-and-budgets.md` | §8–§10, §18 | Writing scenario `checks` paths and operators (`result`, `world`, `calls`, `error`), money/date rules, `--max-calls` ceilings, pure functions, or multi-step state sequences (`$step_result`) |
| `runbook/screens-and-svg.md` | §13, §20 | Building a browser page, UI screen, or interactive visual app: `render` returning `{html}`, `app-map.json` (buttons, keys, `after`, `timers`), `.ui.svg` layout comparison (`pdd test --screen URL --drawing SVG`), and HTML sanitizer rules |
| `runbook/cli-and-ports.md` | §5–§7, §21 | Building a `cli` command (`argv`/`stdout`/`stderr`, `pdd test --target code place-order`), prompt-to-prompt `calls`, `initial_world` saved data, or faking outside ports (SQL, files, SHA-256 `compute`, callbacks, varying replies, factories, MCP Try tools) |
| `runbook/testing-and-simulation.md` | §11, §12, §16, §19 | Running `pdd test` or `pdd lint`, diagnosing a `✗` failure or refusal code, running `pdd simulate` (`--new`, `--cli`, `--serve`), Save as test, or checking known interpreter limits |
| `runbook/replays-and-formal.md` | §17 | Working in code space (PR 2): native vector replay tests, planted-mistake controls, `pdd workflow prove <run> --test CMD --expect TEXT`, `## Rules to check` bounded/solver formal checks, `replay-evidence.json`, and agent thread-limit recovery |
| `runbook/autopilot-and-checklists.md` | §14, §15, §22 | Running the bug reproduction or code-only checker flow, formatting PR 1 / PR 2 `done` summary fields, maintaining `small-change-checklist.json`, running Autopilot core jobs, or coordinating bounded subagent handoffs |

## Core workflow and fast-fail essentials

1. **Order of work:**
   Story (`user_stories/<story>.md`) → prompt (`prompts/<job>.prompt.md` with
   `"status": "draft"` and `"prose_sha256": ""`) → scenario (`tests/<story>.json`,
   or `tests/runtime/<story>.json` / `test/runtime/<story>.json` if the repo
   already keeps its own tests in `tests/` or `test/`) → fill hash → `pdd test` →
   person review/approval → code and native unit/replay tests.
2. **One rule, one prompt (§2):**
   Keep each `.prompt.md` prose body `<= 500` lines and focused on WHAT, WHY,
   and failure edges (never implementation HOW). Prompts never own repository
   test suites.
3. **Strict JSON Schema (§3):**
   Every object schema requires `"type": "object"`, `properties`, `required`,
   and `"additionalProperties": false`. Nullable fields use
   `{"oneOf": [{"type": "string"}, {"type": "null"}]}`, never `["string", "null"]`.
   `$ref`, `$defs`, and `anyOf` are refused inside schemas.
4. **Small scenario steps (§2, §8, §18):**
   Copy every Story criterion word-for-word into `criteria` with straight quotes
   (`"`), and check every criterion with at least one exact operator (`equals`,
   `not_equals`, `one_of`, `count`, `at_least`, `at_most`, `not_contains`,
   `all_in`, `equals_ignore_case`, or structured HTML `exists`). Keep scenarios
   `<= 15` steps and each step to one action or ~10 moves/rows/calls
   (10-minute server step cap).
5. **Expected values (§4):**
   Expected values come from the person and requirements—never edit a test to
   make it pass or copy observed code/simulation output without review.

## Core commands

- Fill draft `prose_sha256` locally (0 AI calls): `pdd test --fill-hash`
- Draft a missing `Runtime interface` block locally (0 AI calls): `pdd interface draft prompts/app.prompt.md`
- Check local schema and `.ui.svg` hygiene offline (0 AI calls): `pdd lint --local`
- Run hosted admission lint only (0 AI calls): `pdd lint place-order`
- List selected upload files and byte sizes offline: `pdd test --files place-order`
- Run full prompt checks (`pdd test` already includes lint; avoid standalone `pdd lint` right before `pdd test`): `pdd test place-order`
- Resume waiting on a saved check batch without resending: `pdd test --read batch-1`
- Open an interactive Simulator session (`--new` reloads changed prompts or `app-map.json`): `pdd simulate place-order --new`
- Execute CLI Story scenarios directly against real code (0 AI calls): `pdd test --target code place-order`

Report pages may show `pdd replay …`. That command does not exist yet.
Use native vector replay tests (`runbook/replays-and-formal.md`) or
`pdd test --target code place-order` for CLI entries.
When reporting a problem with `pdd` itself, follow
[docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).
