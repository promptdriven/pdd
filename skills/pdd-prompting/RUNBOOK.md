# PDD interpreter runbook

Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

## Fast authoring guide (self-contained — stop here for ordinary authoring)

Everything needed to author prompts, Stories, native Short JSON scenarios, CLI commands, and zero-`app-map.json` or compact `app-map.json` Screens is below. **Do NOT bulk-read `runbook/*.md` chapters or run `pdd * --help` upfront**—open a chapter only when a workflow step or specific lint/test error points to it.

1. **Order & scope:** Story (`user_stories/<slug>.md`) → prompt (`prompts/<name>.prompt.md`) → native Short JSON test (`tests/<slug>.json`, or `tests/runtime/<slug>.json` when `tests/` holds native tests) → `pdd files --json && pdd lint --local` → `pdd test` → person approval → code. For single-file UI tryouts, one `prompts/<app>.prompt.md` needs no Story, test, `app-map.json`, or `Runtime interface` (`pdd simulate prompts/<app>.prompt.md`). Author a coupled slice (`1–2` prompts) in `1` session (`0` authoring subagents); parallelize `3+` independent modules only after locking shared contracts; keep verify/formal/review on fresh subagents. Stop at passing `pdd test` unless code was asked; mention `pdd simulate <story>` rather than starting it unless asked.
2. **Prompts (`prompts/<name>.prompt.md`):** Plain Markdown only—**no `<details><summary>Runtime interface</summary>` block** (the Hybrid interpreter runs directly from prose, skips lazy-interface waits, and strips embedded `Runtime interface` blocks from LLM context when present). Keep crisp (`40–120` lines typical, `<= 500` cap, `<= 15` lines/fence, `<= 30` total). Include `# <name>`, purpose, `## Operations and ports` (explicit `sync`/`async` signatures and fields—never bare `object`, list properties + types or say `"open object"`, avoid polymorphic write-port payloads), `## Domain decisions` (invariants, deterministic rules, bounds), failure edges, and `## Dependencies`.
   - **Multi-branch / state rules:** add a short Markdown table or ` ```mermaid ` diagram (`prompt-missing-diagram`).
   - **Single-file plain-prose UI (default — zero `app-map.json`, inline CSS):** declare `render({ state }) -> { state, html }` and `handle_event({ state, event }) -> { state, html }` (or 1-call HTML delta patch `{ state, mode: "patch", base_sha256, edits }`), plus optional pure JSON `apply({ state, event }) -> { state }` for fast logic-only checks in `pdd test`. Always initialize default state when `state` is missing, `null`, or `{}` (the zero-`app-map.json` Simulator opens with `{"state": {}}`). Emit compact semantic HTML (`<button id="..." value="...">`, `<a>`, `<form>`, `data-event-kind="key"`), optional declarative `data-pdd-op="<op>"`, HTML-escaped dynamic text, and inline sanitizer-safe `<style>` (`background-color`, `aria-current="true"`, `display: block` on `<li>`; `<script>` and `on*=` stripped). The interpreter auto-synthesizes a wildcard app map and opens the **Screen** tab. Draw `.ui.svg` **only** when explicitly requested.
   - **CLI apps:** one program prompt (`# <cmd>`), op `main({ argv }) -> { exit_code, stdout, stderr }` (never exit `125`; end output lines with `\n`), persisting via `store.load({ key }) -> { value }` and `store.save({ key, value }) -> { value }`.
3. **Stories (`user_stories/<slug>.md`):** `<= 35` lines; one `"As a …, I want …, so that …"` line; `1..6` numbered criteria starting at `1.` under `## Acceptance criteria`; straight quotes (`"`); plain words (zero file paths, function names, or schema keys).
4. **Native Short JSON tests (`tests/<slug>.json`):** Keep compact Short JSON directly on disk—`/v1/check`, `/v1/lint`, `/v1/try`, and code-space replay accept Short JSON natively (no `v1` expansion loop on disk). Match the Story basename (`user_stories/<slug>.md`), omit `schema_version`, `story_path`, and `criteria` (auto-inferred and bound to `ac-sha256-...` IDs), and set top-level `"entry_path"` (override per step for another prompt; add `"app_maps": ["app-map.json"]` only when using one).
   - **Lean parallel steps (Hybrid 1-pass check):** aim for **1 focused step per criterion** (`5–8` steps typical, `2–4` checks/step, cap `15`, `<= 10` moves/rows/calls per step; omit step `"model"`). Use `seeds` + `from`/`patch` (`"patch"` is RFC 7396 so `null` deletes keys—use `"set": {"/a/b": null}` to keep `null`) so steps run in parallel; chain `{"$step": "id#/field"}` or shared `world` only for persistence.
   - **5-target / 16-operator checks (`"1": [[target, path, op, value], ...]`):** targets `result`, `world`, `calls`, `error`, `input` (never `output`). Exact ops (14): `equals` (`=`), `not_equals` (`!=`), `not_contains`, `count`, `one_of`, `all_in`, `equals_ignore_case`, `at_least` (`>=`), `at_most` (`<=`), `lt` (`<`), `lte`, `gt` (`>`), `gte`, `integer_relation` (plus HTML `exists`). Supplemental (pair with an exact check): `contains` (`contains_all`), non-HTML `exists`. Shorthands: `len>=`, `len<=`, `["error", "=", "bad-input"]`, `["calls", "store.save", "=", 0]`, `["html_exists", "button#start"]`, `["html_text", "span#score", "=", "0"]`, `["html_attr", "button#start", "value", "=", "start"]`, `["html", "button", "labels_include", ["Start"]]`. **HTML selectors MUST include a tag name** (`span#score`, never `#score`).
   - **Compact UI Short JSON example:**
     ```json
     {"entry_path": "prompts/game.prompt.md", "seeds": {"start": {"state": {"score": 0, "status": "ready"}}},
      "steps": [{"id": "open", "op": "render", "input": {"state": {}}, "checks": {"1": [["result", "/state/score", "=", 0], ["html_exists", "button#start"]]}},
                {"id": "play", "op": "handle_event", "from": "start", "patch": {"event": {"kind": "button", "value": "start"}}, "checks": {"2": [["result", "/state/status", "=", "playing"], ["html_text", "span#status", "=", "playing"]]}}]}
     ```
   - **Compact CLI + `store` Short JSON example:**
     ```json
     {"entry_path": "prompts/todo.prompt.md", "initial_world": {"kv": {"tasks": [{"id": 1, "title": "Buy milk", "done": false}]}},
      "simulation": {
        "store.load": {"action": "key-value.get", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": null, "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": null}, "result_value_pointer": "/value"},
        "store.save": {"action": "key-value.put", "world_pointer": "/kv", "key_argument_pointer": "/key", "value_argument_pointer": "/value", "item_key_pointer": null, "item_value_pointer": null, "result_template": {"value": []}, "result_value_pointer": "/value"}
      },
      "steps": [{"id": "done-1", "op": "main", "input": {"argv": ["done", "1"]}, "checks": {"1": [["result", "/exit_code", "=", 0], ["world", "/kv/tasks/0/done", "=", true]]}},
                {"id": "missing", "op": "main", "input": {"argv": ["done", "9"]}, "checks": {"2": [["result", "/exit_code", "=", 1], ["calls", "store.save", "=", 0]]}}]}
     ```
5. **Compact `app-map.json` (optional — only for host `timers`, multi-screen routing, external stylesheets, `after` chains, or strict static `state_schema`):** Omit boilerplate (`schema_version`, `name`, `initial_screen`, `initial_route`, `state_schema`, `synthetic`, `router`, `routes`, `stylesheets`); route controls with `data-pdd-op` or wildcard `"match": {"value": "*"}`:
   ```json
   {"initial_state": {"score": 0, "status": "ready"},
    "screens": [{"prompt_path": "prompts/screen.prompt.md"}],
    "handlers": [{"kind": "button", "match": {"value": "*"}, "handler": {"prompt_path": "prompts/screen.prompt.md", "operation": "handle_event"}}]}
   ```
6. **Expected values (§4):** Expected values come from the person and Story—never edit a test to make it pass or copy observed code/simulation output without review.

## Core commands

- Offline verify (0 AI calls): `pdd files --json && pdd lint --local`
- Hosted admission & whole-program cross-prompt lint (0 AI calls; shared port signatures, mocked-port owner parity, `contracts/*.md` schema reconciliation, unwired advisories): `pdd lint [STORY...]` · Upload preview: `pdd test --files [STORY...]`
- Prompt checks (includes lint + live SSE progress; never run `pdd lint` right before `pdd test`): `pdd test [STORY...]` · Inspect steps/calls/draft interfaces: `pdd test --read <batch> --details`
- Interactive Simulator (Story, repo, or single UI prompt; `--fresh` bypasses cached answers): `pdd simulate [STORY|PROMPT.md] [--new] [--fresh]` · Stop: `pdd simulate --stop [STORY|PROMPT.md]`
- Optional offline tools (0 AI calls): `pdd test --target code <story>` · `pdd lint --emit-v1` · `pdd lint --bind-criteria <story>`

## On-demand deep references (open only when a workflow step or lint/test error points to one)

From the skill folder open `runbook/<file>.md`; from the package root open `skills/pdd-prompting/runbook/<file>.md`:
`runbook/files-and-runtime-block.md` (§1–§4: `$contract`/`$seed`, `pdd-source.json`, approvals `--said`, merges) · `runbook/checks-and-budgets.md` (§8–§10, §18: 5-target/16-op matrix, money/dates, `--max-calls`) · `runbook/screens-and-svg.md` (§13, §20: zero-`app-map.json`, compact `app-map.json`, `data-pdd-op`, inline CSS, `after`, `timers`, `.ui.svg`) · `runbook/cli-and-ports.md` (§5–§7, §21: SQL/blob/hash/varying fakes, `simulation_overrides`, `--target code`) · `runbook/testing-and-simulation.md` (§11–§12, §16, §19: whole-program lint, SSE, `--read --details`, `--fresh`, curl, limits) · `runbook/replays-and-formal.md` (§17: PR 2 replays, formal checks, recovery) · `runbook/autopilot-and-checklists.md` (§14–§15, §22: bug workflow, PR fields, checklists).

Report pages may show `pdd replay …` (not implemented yet; use §17 native vector replays or `pdd test --target code`). Refactoring: [docs/refactor-runbook.md](https://github.com/promptdriven/pdd/blob/main/docs/refactor-runbook.md). Reporting `pdd` issues: [docs/ISSUES.md](https://github.com/promptdriven/pdd/blob/main/docs/ISSUES.md).
