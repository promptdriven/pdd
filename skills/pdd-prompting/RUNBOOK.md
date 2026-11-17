# PDD interpreter runbook

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

## How to use this runbook

Read this index first, then open the 1–2 topic files that match your task or section `§N`.
- From the `pdd-prompting` skill folder (`.../skills/pdd-prompting/RUNBOOK.md`): open `runbook/<file>.md` in the same folder.
- From the `pdd` package root (`.../RUNBOOK.md`, printed by `pdd --help`): open `skills/pdd-prompting/runbook/<file>.md`.

| Topic file | Sections | Open this file when… |
|---|---|---|
| `runbook/files-and-runtime-block.md` | §1–§4 | Writing or editing `prompts/<job>.prompt.md`, `user_stories/<story>.md`, `tests/<story>.json`, strict JSON Schemas, `$contract` / `$seed` references, expected values, or recording chat approvals / requested merges |
| `runbook/checks-and-budgets.md` | §8–§10, §18 | Writing scenario `checks` paths and operators (`result`, `world`, `calls`, `error`), money/date rules, `--max-calls` ceilings, pure functions, or multi-step state sequences (`$step_result`) |
| `runbook/screens-and-svg.md` | §13, §20 | Building a browser page, UI screen, or interactive visual app: `render` returning `{html}`, `app-map.json` (buttons, keys, `after`, `timers`), `.ui.svg` layout comparison (`pdd test --screen URL --drawing SVG`), and HTML sanitizer rules |
| `runbook/cli-and-ports.md` | §5–§7, §21 | Building a `cli` command (`argv`/`stdout`/`stderr`, `pdd test --target code place-order`), prompt-to-prompt `calls`, `initial_world` saved data, or faking outside ports (SQL, files, SHA-256 `compute`, callbacks, varying replies, factories, MCP Try tools) |
| `runbook/testing-and-simulation.md` | §11, §12, §16, §19 | Running `pdd test` or `pdd lint`, diagnosing a `✗` failure or refusal code, running `pdd simulate` (`--new`, `--cli`, `--serve`), Save as test, curl against Try, or checking known interpreter limits |
| `runbook/replays-and-formal.md` | §17 | Working in code space (PR 2): native vector replay tests (`BigInt` whole numbers, planted-mistake control), `pdd workflow prove <run> --test CMD --expect TEXT`, formal checks from `.prompt.md` and `## Rules to check`, `replay-evidence.json`, and `agent thread limit reached` recovery |
| `runbook/autopilot-and-checklists.md` | §14, §15, §22 | Running the bug reproduction or code-only checker flow, formatting PR 1 / PR 2 `done` summary fields, maintaining `small-change-checklist.json`, running Autopilot core jobs, or coordinating bounded subagent handoffs |

## Core workflow and fast-fail essentials

1. **Order of work and coupling (§1, §2, §22):** Story (`user_stories/<story>.md`) → prompt (`prompts/<job>.prompt.md`) → scenario (`tests/<story>.json`, or `tests/runtime/<story>.json` / `test/runtime/<story>.json` when `tests/` or `test/` holds native tests) → `pdd files` + `pdd lint --local` → `pdd test` → person approval → code and native replay tests. Use `0` Stories + one `"No Story: <reason>"` PR line for internal changes, edit the existing Story when changing an existing slice, or write `1` Story per cohesive standalone user loop. Author a single coupled slice (`1–2` prompts) in `1` session (`0` authoring subagents); for `3+` independent modules, lock shared contracts (`app-map.json` / interfaces) first, then parallelize prompt workers; keep code verification and review on fresh independent subagents.
2. **One rule, one prompt (§2):** Keep each `.prompt.md` prose body `<= 500` lines and focused on WHAT, WHY (`## Domain decisions`, including technical invariants and edge bounds), and failure edges (never implementation HOW, and never link `kind: native-only` adapters under `## Dependencies` of checkable prompts). Prompts never own repository test suites.
3. **Strict JSON Schema and shared contracts (§2, §3):** Every object schema requires `"type": "object"`, `properties`, `required`, and `"additionalProperties": false`. Nullable fields use `{"oneOf": [{"type": "string"}, {"type": "null"}]}`, never `["string", "null"]`. `$ref`, `$defs`, and `anyOf` are refused inside schemas; use `$contract` for shared schemas and `$seed` for shared `initial_world` seeds.
4. **1 observable check per material claim and tight budgets (§2, §8, §10, §13, §18, §20):** Copy every Story criterion word-for-word into `criteria` with straight quotes (`"`), and write `1` observable check per material claim using an exact operator (`equals`, `not_equals`, `one_of`, `count`, `at_least`, `at_most`, `not_contains`, `all_in`, `equals_ignore_case`, or HTML `exists`). Keep scenarios `<= 15` steps (`~10` moves/rows/calls per step; omit optional step `"model"` unless testing model choice), check structured state fields and key controls on dense grids instead of huge HTML strings, and render `.ui.svg` to PNG only when a person explicitly asks.
5. **Expected values (§4):** Expected values come from the person and Story—never edit a test to make it pass or copy observed code/simulation output without review.

## Core commands

- Check local Story, `app-map.json`, scenario schema, and `.ui.svg` hygiene offline (0 AI calls): `pdd lint --local`
- Run hosted admission lint only (0 AI calls): `pdd lint place-order`
- List selected upload files and byte sizes offline: `pdd test --files place-order`
- Run full prompt checks (`pdd test` already includes lint; avoid standalone `pdd lint` right before `pdd test`): `pdd test place-order`
- Resume waiting on a saved check batch without resending: `pdd test --read batch-1`
- Open an interactive Simulator session (`--new` reloads changed prompts or `app-map.json`): `pdd simulate place-order --new`
- Execute CLI Story scenarios directly against real code (0 AI calls): `pdd test --target code place-order`

Report pages may show `pdd replay …`. That command does not exist yet. Use native vector replay tests (`runbook/replays-and-formal.md`) or `pdd test --target code place-order` for CLI entries. For structural cleanup and refactoring passes without behavior drift, follow [docs/refactor-runbook.md](https://github.com/promptdriven/pdd/blob/main/docs/refactor-runbook.md). When reporting a problem with `pdd` itself, follow [docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).
