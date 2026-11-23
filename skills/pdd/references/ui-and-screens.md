# UI screens, `.ui.svg` mockups, and `pdd sim`

Start every single-screen interactive UI with **one plain-prose `.prompt.md` and zero `app-map.json`**. Add `app-map.json` or `.ui.svg` mockups only when the app genuinely needs them. Backend servers, routers, CLIs, and daemons stay screenless.

## 1. Single-file plain-prose UI (default)

Write one plain-Markdown prompt with:

- **`render({ state }) -> { state, html }`**: initializes default state when `state` is missing, `null`, or `{}` (the zero-`app-map.json` Simulator opens with `{"state": {}}`). Returns compact semantic HTML (`<button id="..." value="...">`, `<a>`, `<form>`, `data-event-kind="key"`, optional `data-pdd-op="<op>"`) with HTML-escaped dynamic text and inline sanitizer-safe `<style>`.
- **`handle_event({ state, event }) -> { state, html }`**: handles clicks, form submits, keyboard shortcuts, and declarative `data-pdd-op` actions in one call. For large screens, may return an HTML delta patch `{ state, mode: "patch", base_sha256, edits }`.
- **Optional `apply({ state, event }) -> { state }`**: pure JSON state-transition op for fast logic-only checks in `pdd test` without HTML tokens.

Run it immediately with `pdd sim prompts/<app>.prompt.md` (no Story, test file, or `app-map.json` required). The Simulator synthesizes a wildcard map and opens on the **Screen** tab.

### HTML sanitizer & CSS rules

- Preserved: inline `<style>` (CSS variables, `@keyframes`, `:hover`/`:focus`/`:active`), semantic HTML, `data-pdd-op`, `data-event-kind`.
- Stripped: `<script>`, `<iframe>`, `on*=` attributes, `javascript:` URLs, external `@import`, and `url(...)` loads.
- Prefer `background-color` (not `background`), `aria-current="true"` (not `aria-pressed`), and `display: block` on `<li>` (not `list-style`).

## 2. Optional compact `app-map.json`

Add `app-map.json` (or `app/app-map.json`) **only** when the UI needs host `timers`, multi-screen routing, external `stylesheets`, follow-up `after` handlers, `.ui.svg` mockup screens, or strict static `state_schema`. Omit optional defaults (`schema_version`, `name`, `initial_screen`, `initial_route`, `state_schema`, `synthetic`, `router`, `routes`, `stylesheets`) and use wildcard `"match": {"value": "*"}`:

```json
{
  "initial_state": {"score": 0, "status": "ready"},
  "screens": [{"prompt_path": "prompts/screen.prompt.md"}],
  "handlers": [{"kind": "button", "match": {"value": "*"}, "handler": {"prompt_path": "prompts/screen.prompt.md", "operation": "handle_event"}}]
}
```

- **Host timers (`timers`):** optional root array (`<= 16` timers, `<= 1` per screen, `interval_ms` integer `1000..3600000`) with `id`, `screen`, `interval_ms`, `enabled_pointer` (Boolean), `generation_pointer` (integer), `handler`, `input`, `state`, `next` (and optional `after`). Omit `timers` unless automatic ticks are requested; prefer `handle_event` over separate `apply`+`render` handlers in `app-map.json` (avoids 2× calls per click), and keep grid HTML compact (avoid verbose per-cell attributes).
- **Follow-up `after` handlers:** chain a secondary operation after a handler and bind its result into state via `"bind": "/path"`.
- Run `pdd sim <story> --new` after changing prompts or `app-map.json` so the Simulator uploads the new version.

## 3. Optional `.ui.svg` mockups

Draw `.ui.svg` mockups (`views/<state>[--<variant>]__<layout-mode>.ui.svg`) only when requested or designing multi-view layouts:

- Link under `## Appearance` using Markdown image syntax `![Alt text](views/...)` (never plain `[label](...)` outside `## Dependencies`).
- SVG owns visual layout, visible labels, spatial order, and stable intent `id`s (`viewBox`, `<title>`, `<desc>`; mark surroundings `data-context-only="true"` or `class="context-only"`; no scripts, event handlers, external fonts, or base64 blobs). Prose owns behavior, responsive rules, focus order, and dynamic data.
- **Local `pdd lint` alignment contract:** every layout `id="<name>"` in `.ui.svg` must be acknowledged in `## Appearance` via backticks (`` `<name>` ``) or `<name> region|box|bar|container|button|grid|heading|label` (avoid decorative `id`s on background rects/dividers); every non-numeric `<text>` label must appear in the prompt prose; and every interactive control declared in prose must have matching `<text>` or `id` in `.ui.svg`.
- Declare **illustrative** vs **comparison reference** and fidelity (**Relational**, **Measured**, or **Exact**).
- Verify layout alignment offline with `pdd lint` (`<150ms`, 0 AI calls); compare a live browser render with `pdd test --screen URL --drawing PATH [--look]`.

## 4. HTML checks and Simulator rules

- **HTML checks** (always include a tag name in selectors, e.g. `span#score`, never `#score`): `["html_exists", "button#start"]`, `["html_text", "span#score", "=", "42"]`, `["html_attr", "button#start", "value", "=", "start"]`, `["html", "button", "labels_include", ["Start", "Pause"]]`.
- **Link privacy:** show Simulator URLs only to the person — **never** paste them into files, PRs, issues, or shared channels.
- **Save as test:** only the person saves cases in the Simulator. Pull saved cases back with `pdd sim <story>`, verify every criterion has an exact check, and review expected values with the person.
- Never launch an interactive Simulator session unless the person asks; recommend `pdd sim <story>` during the pre-code check.
