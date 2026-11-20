# Runbook: Screens, App Maps, SVG Layout, and HTML Checks

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 13. Give your app a screen (app map)

The Simulator has a **Screen** tab only when the repo has an app map (`app-map.json`, or `app/app-map.json`). For a page or screen prompt, include a `render` operation returning `{"html": string}` with semantic HTML, CSS classes, unique button `id` and `value` attributes, and no `<script>` or inline handlers. Author `.ui.svg` layout drawings only when requested or designing multi-view layouts: Its `## Appearance` section links the mockups, and `pdd lint --local` checks SVG geometry/overflow offline (render PNGs only when asked; compare live renders with `pdd test --screen URL --drawing SVG`).

### App map

- `pdd simulate <story> --new` loads `app-map.json` (or `--app-map PATH`). Without `--new`, pdd reuses the open simulation and does not send the map.
- Ordinary `pdd lint <story>` checks the Story's prompts and scenario (unless the scenario declares `"app_maps": ["app-map.json"]`); `pdd simulate <story> --new` checks `app-map.json` before starting Try.
- Every object in `state_schema` follows §3 (`additionalProperties: false`, `required`, no `["string", "null"]`). Match all buttons on one screen consistently by `"value"`.

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

- **HTML sanitizer rules:** `<script>`, `<iframe>`, `on*=` handlers, and `javascript:` URLs are stripped (this does not disable host `timers`). Use `background-color` (not `background`), `aria-current="true"` (not `aria-pressed`), and `display: block` on `<li>` (not `list-style`).
- **HTML checks (always include a tag name in selectors, e.g. `button#start`, `span#score`, never bare `#score`):**
  - `["html_exists", "button#start"]` (exact check)
  - `["html_text", "span#score", "=", "42"]`
  - `["html_attr", "button#start", "value", "=", "start"]`
  - `["html", "button", "labels_include", ["Start", "Pause"]]`
- On dense boards/grids, assert exact structured state fields on logic operations and key controls/readouts on the render operation rather than huge HTML strings.
