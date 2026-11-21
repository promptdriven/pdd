# Runbook: Screens, App Maps, SVG Layout, and HTML Checks

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 13. Give your app a screen (app map)

The Simulator opens on the **Screen** tab automatically for both a **single-file plain-prose UI** (zero `app-map.json`, zero `Runtime interface`, optional Story: run `pdd simulate prompts/<app>.prompt.md` or `pdd simulate` in a single-prompt repo) and a repo with an explicit **app map** (`app-map.json`, or `app/app-map.json`).

- **Single-file plain-prose UI (default for single-screen interactive apps):** write one plain-Markdown prompt with:
  - `render({ state }) -> { state, html }`: initializes default state when `state` is missing, `null`, or `{}` (the zero-`app-map.json` Simulator opens with `{"state": {}}`), and returns semantic HTML (inline sanitized `<style>` is preserved) with HTML-escaped dynamic text, unique button `id`/`value` attributes, and no `<script>` or inline `on*=` handlers.
  - `handle_event({ state, event }) -> { state, html }` (1-call turn contract): handles clicks, form submits, keyboard shortcuts (`data-event-kind="key"`), and declarative `data-pdd-op="<op>"` actions with automatic wildcard event admission. To avoid re-emitting a full page on large screens, `handle_event` may return an HTML delta patch `{ state, mode: "patch", base_sha256, edits }`.
  - Optional pure JSON `apply({ state, event }) -> { state }` for fast logic-only state-transition checks in `pdd test` (zero HTML output tokens).
- **When to add `app-map.json`:** add `app-map.json` (or `app/app-map.json`) when the app needs host `timers`, multi-screen navigation/routing, external `stylesheets`, follow-up `after` chains, explicit static `state_schema`, or `.ui.svg` layout mockups. Author `.ui.svg` layout drawings only when requested or designing multi-view layouts: Its `## Appearance` section links the mockups, and `pdd lint --local` checks SVG geometry/overflow offline (render PNGs only when asked; compare live renders with `pdd test --screen URL --drawing SVG`).

### App map

- `pdd simulate <story> --new` loads `app-map.json` (or `--app-map PATH`). Without `--new`, pdd reuses the open simulation and does not send the map.
- Ordinary `pdd lint <story>` checks the Story's prompts and scenario (unless the scenario declares `"app_maps": ["app-map.json"]`); `pdd simulate <story> --new` checks `app-map.json` before starting Try.
- **Compact `app-map.json` defaults:** `schema_version` is optional (defaults to `prompt-runtime.app-map.v2`; both `v1` and `v2` are accepted), and `name`, `initial_screen` (defaults to the first screen), `initial_route`, `synthetic`, `router`, `routes`, `stylesheets`, and `state_schema` (synthesized from `initial_state`) may all be omitted. Screen `id` defaults to `"main"` / `"screen-N"`, `source` defaults to `"operation"`, and `format` defaults to `"svg"` for mockups else `"html"`. Prompts referenced by `app-map.json` need no `Runtime interface` block. Use wildcard `"match": {"value": "*"}` when one handler dispatches all buttons on a screen.
- When an explicit `state_schema` is provided, every object follows §3 (`additionalProperties: false`, `required`, no `["string", "null"]`). Match explicit per-button handlers on one screen consistently by `"value"`.

An app map with a follow-up `after` step (`app-map.json`):
```json
{"schema_version": "prompt-runtime.app-map.v1", "name": "Machine Desk", "initial_screen": "desk", "initial_route": null,
 "initial_state": {"draft": "ping", "panel": {"sent": 0, "reply": {"status": "idle"}}},
 "state_schema": {"type": "object", "properties": {
   "draft": {"type": "string"},
   "panel": {"type": "object", "properties": {
     "sent": {"type": "integer"},
     "reply": {"type": "object", "properties": {"status": {"type": "string"}},
       "required": ["status"], "additionalProperties": false}},
     "required": ["sent", "reply"], "additionalProperties": false}},
   "required": ["draft", "panel"], "additionalProperties": false},
 "synthetic": true, "router": null, "routes": [], "stylesheets": [],
 "screens": [{"id": "desk", "prompt_path": "prompts/desk_screen.prompt.md", "operation": "render", "source": "operation",
   "format": "html", "input": {"draft": {"$ref": "/state/draft"}, "panel": {"$ref": "/state/panel"}}, "result_pointer": "/html"}],
 "handlers": [{"screen": "desk", "kind": "button", "match": {"value": "send-ping"},
   "handler": {"prompt_path": "prompts/machine_box.prompt.md", "operation": "send"},
   "input": {"message": {"$ref": "/state/draft"}},
   "next": {"kind": "same", "screen": null, "route_pointer": null},
   "state": {"draft": "", "panel": {"sent": {"$ref": "/result/sent"}, "reply": {"$ref": "/state/panel/reply"}}},
   "after": [{"handler": {"prompt_path": "prompts/reply_box.prompt.md", "operation": "read_reply"},
     "input": {"sent": {"$ref": "/result/sent"}, "previous": {"$ref": "/state/panel/reply/status"}},
     "bind": "/panel/reply"}]}]}
```

- **Mockup screens (`"source": "mockup"`):** set `"prompt_path"` to a prompt whose `## Appearance` links `.ui.svg` files, with `"operation": null`, `"format": "svg"`, and `"result_pointer": null`.
- **Host timers (`timers`):** optional root array (at most `16` timers, at most one per non-wildcard screen; `interval_ms` is a strict integer `1000..3600000`) driving timed behavior without page `<script>`. Each timer has exact fields `id`, `screen`, `interval_ms`, `enabled_pointer` (required Boolean state field), `generation_pointer` (required integer `0..9007199254740991`), `handler`, `input` (may copy `/state/...` or proved `/event/<field>` from `{timer_id, generation, sequence, elapsed_ms}`), `state`, `next` (and optional `after`):
  `{"id": "order-refresh", "screen": "cart", "interval_ms": 1000, "enabled_pointer": "/polling", "generation_pointer": "/generation", "handler": {"prompt_path": "prompts/cart.prompt.md", "operation": "refresh_status"}, "input": {"state": {"$ref": "/state"}, "generation": {"$ref": "/event/generation"}}, "state": {"$ref": "/result/state"}, "next": {"kind": "same", "screen": null, "route_pointer": null}}`

### .ui.svg local lint contract

- **Image syntax outside `## Dependencies`:** link `.ui.svg` files as `![label](views/...)`—plain `[label](...)` links outside `## Dependencies` are skipped by scoped uploads (`link syntax` / `dependency-file-unreadable`).
- **Visible `id="<name>"` (`region #<name>`):** every non-hidden `id` (outside `<defs>` and without `data-context-only="true"` / class `context-only`) must appear in `## Appearance` in backticks (`` `<name>` ``) or in prose as `<name> region|box|bar|container|button|grid|heading|label`; omit decorative `id`s on background rects/dividers.
- **Visible non-numeric `<text>` labels:** every non-numeric `<text>` (outside `[\d\s.,+%-]+`) must appear in `.prompt.md` prose (`drawing label absent from prompt`).
- **Interactive controls:** every button/control named in `.prompt.md` (scoped per view when multiple `.ui.svg` drawings are linked) must match a visible `<text>` or `id` in `.ui.svg` (`prompt control absent from drawing`).

## 20. HTML checks and Simulator rendering

- **Inline CSS & declarative controls:** sanitized inline `<style>` tags are preserved (safe selectors, CSS variables, `@keyframes`, `:hover`/`:focus`/`:active`; external `@import`, `url(...)` loads, and `expression()` are stripped). Declarative `data-pdd-op="<op>"` attributes, `data-event-kind="key"`, and native `<button>` / `<form>` / `<a>` controls route events without page scripts.
- **HTML sanitizer rules:** `<script>`, `<iframe>`, `on*=` handlers, and `javascript:` URLs are stripped (this does not disable `handle_event` or host `timers`). Use `background-color` (not `background`), `aria-current="true"` (not `aria-pressed`), and `display: block` on `<li>` (not `list-style`).
- **1-call HTML delta patching:** `handle_event` may return `{ state, mode: "patch", base_sha256, edits }` to patch existing screen DOM nodes in place instead of re-emitting full HTML on every click.
- **HTML checks (always include a tag name in selectors, e.g. `button#start`, `span#score`, never bare `#score`):**
  - `["html_exists", "button#start"]` (exact check)
  - `["html_text", "span#score", "=", "42"]`
  - `["html_attr", "button#start", "value", "=", "start"]`
  - `["html", "button", "labels_include", ["Start", "Pause"]]`
- On dense boards/grids, assert exact structured state fields on logic operations and key controls/readouts on the render operation rather than huge HTML strings.
