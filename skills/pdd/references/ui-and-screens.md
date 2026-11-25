# UI screens, `.ui.svg` drawings, and running UI prompts directly

Write every interactive UI screen as plain-prose Markdown paired with a `.ui.svg` layout drawing (linked under `## Appearance`) so its layout stays consistent across runs. Backend servers, APIs, routers, CLIs, and daemons stay screenless.

## 1. Plain-prose UI screen prompt

Write one plain-Markdown prompt (for a single screen) with:

- **`render({ state }) -> { state, html }`**: initializes default state when `state` is missing, `null`, or `{}` (the Prompt Interpreter opens with `{"state": {}}`). Returns compact semantic HTML (`<button id="..." value="...">`, `<a>`, `<form>`, `data-event-kind="key"`, optional `data-pdd-op="<op>"`) with HTML-escaped dynamic text and inline sanitizer-safe `<style>`.
- **`handle_event({ state, event }) -> { state, html }`**: handles clicks, form submits, keyboard shortcuts, and declarative `data-pdd-op` actions in one call. For large screens, may return an HTML delta patch `{ state, mode: "patch", base_sha256, edits }`. Keep grid HTML compact (avoid verbose per-cell attributes).
- **Optional `apply({ state, event }) -> { state }`**: pure JSON state-transition op for fast logic-only checks in `pdd test` without HTML tokens.

A person can try it right away with `pdd prompts/<app>.prompt.md` (no Story or test file required); it opens on the **Screen** tab. Run `pdd <story> --new` (or `pdd prompts/<app>.prompt.md --new`) after changing prompts so the Prompt Interpreter uploads the new version. Agents recommend this command during the pre-code check and launch it only when asked.

### HTML sanitizer & CSS rules

- Preserved: inline `<style>` (CSS variables, `@keyframes`, `:hover`/`:focus`/`:active`), semantic HTML, `data-pdd-op`, `data-event-kind`.
- Stripped: `<script>`, `<iframe>`, `on*=` attributes, `javascript:` URLs, external `@import`, and `url(...)` loads.
- Prefer `background-color` (not `background`), `aria-current="true"` (not `aria-pressed`), and `display: block` on `<li>` (not `list-style`).

## 2. `.ui.svg` layout drawings

Draw a `.ui.svg` layout (`views/<state>[--<variant>]__<layout-mode>.ui.svg`) for every UI screen unless the person asks to skip it:

- Link under `## Appearance` using Markdown image syntax `![Alt text](views/...)` (never plain `[label](...)` outside `## Dependencies`).
- SVG owns visual layout, visible labels, spatial order, and stable intent `id`s (`viewBox`, `<title>`, `<desc>`; mark surroundings `data-context-only="true"` or `class="context-only"`; no scripts, event handlers, external fonts, or base64 blobs). Prose owns behavior, responsive rules, focus order, and dynamic data.
- **Local `pdd lint` alignment contract:** every layout `id="<name>"` in `.ui.svg` must be acknowledged in `## Appearance` via backticks (`` `<name>` ``) or `<name> region|box|bar|container|button|grid|heading|label` (avoid decorative `id`s on background rects/dividers); every non-numeric `<text>` label must appear in the prompt prose; and every interactive control declared in prose must have matching `<text>` or `id` in `.ui.svg`.
- **Inline `<svg>` charts/diagrams:** map domain values into a fixed human-aspect `viewBox` (e.g. `viewBox="0 0 600 240"`, `preserveAspectRatio="xMidYMid meet"`) with explicit `stroke-width` / `fill` — never place raw unscaled domain numbers into `viewBox`.
- Declare **illustrative** vs **comparison reference** and fidelity (**Relational**, **Measured**, or **Exact**).
- Verify layout alignment offline with `pdd lint` (`<150ms`, 0 AI calls); compare a live browser render with `pdd test --screen URL --drawing PATH [--look]`.

## 3. HTML checks and Prompt Interpreter rules

- **HTML checks** (always include a tag name in selectors, e.g. `span#score`, never `#score`): `["html_exists", "button#start"]`, `["html_text", "span#score", "=", "42"]`, `["html_attr", "button#start", "value", "=", "start"]`, `["html", "button", "labels_include", ["Start", "Pause"]]`.
- **Link privacy:** show Prompt Interpreter URLs only to the person — **never** paste them into files, PRs, issues, or shared channels.
- **Save as test:** only the person saves cases in the Prompt Interpreter. Pull saved cases back with `pdd <story>`, verify every criterion has an exact check, and review expected values with the person.
- Never launch an interactive Prompt Interpreter session unless the person asks; recommend `pdd <story>` (or `pdd prompts/<app>.prompt.md`) during the pre-code check.
