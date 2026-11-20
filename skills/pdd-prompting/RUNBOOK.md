# PDD interpreter runbook

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

## Fast authoring guide (self-contained — stop here for ordinary authoring)

Everything needed to author prompts, Stories, Short JSON scenarios, CLI commands, and Screen `app-map.json` is right below. **Do NOT bulk-read `runbook/*.md` chapters or run `pdd * --help` upfront**—open a chapter in the footer only if a workflow step or a specific lint/test error calls for it.

1. **Order & scope:** Story (`user_stories/<slug>.md`) → prompt (`prompts/<name>.prompt.md`) → test (`tests/<slug>.json`, or `tests/runtime/<slug>.json` when `tests/` holds native tests) → `pdd files --json` + `pdd lint --local` → `pdd test` → person approval → code. Author a single coupled slice (`1–2` prompts) in `1` session (`0` authoring subagents); for `3+` independent modules, lock shared contracts first, then parallelize; keep code verification/review on fresh independent subagents. Stop at passing `pdd test` unless code was asked; mention `pdd simulate <story>` in text instead of starting it unless asked.
2. **Prompts (`prompts/<name>.prompt.md`):** Plain Markdown only—**no `<details><summary>Runtime interface</summary>` block** (the interpreter synthesizes schemas from prose). Keep crisp (`40–120` lines typical, `<= 500` cap, `<= 15` lines per fence / `<= 30` total). Include `# <name>`, purpose, `## Domain decisions` (invariants, deterministic rules, bounds), explicit op input/output/error/port fields (never bare `object`—list properties + types or say `"open object"`; avoid polymorphic write-port payloads), failure edges, and `## Dependencies`.
   - **Multi-branch / state-transition rules:** include a short Markdown decision table or ` ```mermaid ` diagram so `pdd lint --local` stays clean (`prompt-missing-diagram`).
   - **Screen render prompts:** take structured state, return `{"html": string}` (semantic HTML + CSS classes only; no `<script>`, no inline `onclick=`/`style=`; unique `id` and `value` on every `<button>`). Draw `.ui.svg` **only** when explicitly requested.
   - **CLI apps:** one program prompt (`# <cmd>`), operation `main` taking `{"argv": string[]}` returning `{"exit_code": integer, "stdout": string, "stderr": string}` (never exit `125`; every output line ends with `\n`), persisting via `store.load({ key }) -> { value }` and `store.save({ key, value }) -> { value }`.
3. **Stories (`user_stories/<slug>.md`):** `<= 35` lines; one `"As a …, I want …, so that …"` line; `1..6` numbered criteria starting at `1.` under `## Acceptance criteria`; straight quotes (`"`); plain words (zero file paths, function names, or schema keys).
4. **Short JSON tests (`tests/<slug>.json`):** Match the Story basename (`user_stories/<slug>.md`). Omit `schema_version`, `story_path`, and `criteria` so PDD binds `1..N` to `ac-sha256-...` IDs automatically. Set top-level `"entry_path"` (override per step for a second prompt like `prompts/screen.prompt.md`); add `"app_maps": ["app-map.json"]` for visual apps.
   - **Keep scenarios lean and parallel:** aim for **1 focused step per Story criterion** (`5–8` steps typical, `2–4` checks per step, hard cap `15`; omit step `"model"`). Give each step self-contained state (`seeds` + `from`/`patch`; `"patch"` is RFC 7396 so `null` deletes keys—use `"set": {"/a/b": null}` to keep `null`) so steps run in parallel; chain `{"$step": "id#/field"}` or shared `world` only for persistence criteria.
   - **Check tuples (`"1": [[target, path, op, value], ...]`):** `=` (`equals`), `!=`, `>=`, `<=`, `len>=`, `len<=`, `one_of`, `count`, `not_contains`, `all_in`, `equals_ignore_case`, `contains` (pair with an exact check), `contains_all`. Shorthands: `["error", "=", "bad-input"]`, `["calls", "store.save", "=", 0]` (mutating ops only), `["html_exists", "button#start"]`, `["html_text", "span#score", "=", "0"]`, `["html_attr", "button#start", "value", "=", "start"]`, `["html", "button", "labels_include", ["Start"]]`. **HTML selectors MUST include a tag name** (`span#score`, `button#left`, never bare `#score`).
   - **Compact Short JSON example (CLI with `store`):**
     ```json
     {"entry_path": "prompts/todo.prompt.md", "initial_world": {"kv": {"tasks": [{"id": 1, "title": "Buy milk", "done": false}]}},
      "simulation": {
        "store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": null}, "result_value_pointer": "/value"},
        "store.save": {"action": "key-value.put", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": "/value", "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": []}, "result_value_pointer": "/value"}
      },
      "steps": [{"id": "done-1", "op": "main", "input": {"argv": ["done", "1"]}, "checks": {"1": [["result", "/exit_code", "=", 0], ["world", "/kv/tasks/0/done", "=", true]]}},
                {"id": "missing", "op": "main", "input": {"argv": ["done", "9"]}, "checks": {"2": [["result", "/exit_code", "=", 1], ["calls", "store.save", "=", 0]]}}]}
     ```
   - **If `program-scenario.v1` JSON is required on disk:** write Short JSON first (omitting `"criteria"`), then run `pdd lint --emit-v1 --write` (never `> file` or `node -e` scripts)—it compiles to canonical `program-scenario.v1` and binds `ac-sha256-...` criterion IDs in place in one command.
5. **Screen `app-map.json` (visual apps only):** Strict JSON Schema (`"type": "object"`, `properties`, `required`, `"additionalProperties": false`; nullable uses `{"oneOf": [{"type": "string"}, {"type": "null"}]}`, never `["string", "null"]`; no `$ref`/`$defs`/`anyOf`). Sanitizer-safe CSS (`background-color` not `background`, `aria-current="true"` not `aria-pressed`, `display:block` on `<li>` not `list-style`). Match all buttons on a screen by `"value"`:
   ```json
   {"schema_version": "prompt-runtime.app-map.v1", "name": "Game", "initial_screen": "board", "initial_route": null,
    "initial_state": {"score": 0, "status": "ready"},
    "state_schema": {"type": "object", "properties": {"score": {"type": "integer"}, "status": {"type": "string", "enum": ["ready", "playing"]}}, "required": ["score", "status"], "additionalProperties": false},
    "synthetic": true, "router": null, "routes": [], "stylesheets": ["prompts/screen.css"],
    "screens": [{"id": "board", "prompt_path": "prompts/screen.prompt.md", "operation": "render", "source": "operation", "format": "html", "input": {"score": {"$ref": "/state/score"}, "status": {"$ref": "/state/status"}}, "result_pointer": "/html"}],
    "handlers": [{"screen": "board", "kind": "button", "match": {"value": "start"}, "handler": {"prompt_path": "prompts/game.prompt.md", "operation": "start"}, "input": {"status": {"$ref": "/state/status"}}, "next": {"kind": "same", "screen": null, "route_pointer": null}, "state": {"score": {"$ref": "/result/score"}, "status": {"$ref": "/result/status"}}}]}
   ```
6. **Expected values (§4):** Expected values come from the person and Story—never edit a test to make it pass or copy observed code/simulation output without review.

## Core commands

- Offline verify (0 AI calls): `pdd files --json && pdd lint --local`
- Compile Short JSON to `program-scenario.v1` in place + verify (0 AI calls): `pdd lint --emit-v1 --write && pdd files --json && pdd lint --local`
- Bind legacy Story criterion IDs on disk (0 AI calls): `pdd lint --bind-criteria <story>`
- Hosted admission lint only (0 AI calls): `pdd lint <story>` · List upload files: `pdd test --files <story>`
- Run prompt checks (`pdd test` includes lint; do not run `pdd lint` right before `pdd test`): `pdd test <story>` · Resume batch: `pdd test --read batch-1`
- Interactive Simulator: `pdd simulate <story> --new` · CLI code replay (0 AI calls): `pdd test --target code <story>`

## On-demand deep references (open only when a workflow step or lint/test error points to one)

From the skill folder open `runbook/<file>.md`; from the package root open `skills/pdd-prompting/runbook/<file>.md`:
`runbook/files-and-runtime-block.md` (§1–§4: `$contract`/`$seed`, `pdd-source.json`, approvals `--said`, merges) · `runbook/checks-and-budgets.md` (§8–§10, §18: advanced check paths, money/dates, `--max-calls`) · `runbook/screens-and-svg.md` (§13, §20: `after`, `timers`, `.ui.svg` layout comparison) · `runbook/cli-and-ports.md` (§5–§7, §21: SQL/blob/hash/varying fakes, `simulation_overrides`, `--target code`) · `runbook/testing-and-simulation.md` (§11–§12, §16, §19: failure diagnosis, curl, limits) · `runbook/replays-and-formal.md` (§17: PR 2 replays, formal checks, recovery) · `runbook/autopilot-and-checklists.md` (§14–§15, §22: bug workflow, PR fields, checklists).

Report pages may show `pdd replay …` (not implemented yet; use §17 native vector replays or `pdd test --target code`). Refactoring: [docs/refactor-runbook.md](https://github.com/promptdriven/pdd/blob/main/docs/refactor-runbook.md). Reporting `pdd` issues: [docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).
