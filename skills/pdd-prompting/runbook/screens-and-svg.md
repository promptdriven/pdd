# Runbook: Screens, App Maps, SVG Layout, and HTML Checks

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 13. Give your app a screen (app map)

### The drawing is the layout spec

When a screen prompt links a `.ui.svg`, declare its purpose: illustrative content or a comparison-reference state.
The SVG owns appearance. Prose owns behavior, accessibility and the authority for actual values. Illustrative sample
values do not become required runtime values. For a comparison reference, declare the state and its values so the
page can reproduce them. Prose and drawing must agree on owned parts, visible words, spatial order and stable ids.

Declare ownership, state, reference viewport, fidelity, comparator and tolerances beside the view. The reference
viewport is a comparison condition, not a fixed runtime screen size. Name each region/control id in the appearance
rules. Mark unowned surroundings `data-context-only="true"` or class `context-only`. Keep DOM/focus order in
accessibility prose; SVG source order does not set it. Preserve the declared fidelity and comparison requirements
when a tool cannot check them; report that gap instead of treating admission as proof.

Before building, run `pdd lint --local` (or add Story names) to see local SVG warnings with 0 AI calls and no network. It checks explicit control names, visible labels and named layout regions in both directions, and warns when an HTML operation screen with a linked `.ui.svg` drawing has `"stylesheets": []` in its app map or names none of the CSS classes in its stylesheet. A generic score field does not specify a drawn score box. Static vocabulary matching is advice: warnings name unmatched parts and never block or approve a prompt. Ordinary `pdd lint` and `pdd test` include this advice before server work. Resolve disagreements by making the prompt, stylesheet and drawing agree with the requested design.

Build reads the linked drawing as the layout spec under its declared purpose and fidelity. For a comparison-reference state, implement its required parts, words, ids and order. After building, serve the real page in that state and run:

```sh
pdd test --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg
pdd test --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg --look
```

This uses installed headless Chrome/Chromium at the SVG viewport, no AI or interpreter calls. Set `PDD_CHROME_PATH` if the executable is not found. It checks every visible text occurrence and id, including numeric values, against the real page; metadata, hidden and context-only SVG subtrees are excluded. It requires visible page parts, center positions within 15% of each viewport dimension, and the same spatial order for separated parts. Adding `--look` also checks the main canvas color, painted card/section/control boxes (bare text inside an unstyled box fails), box dimensions and spacing between adjacent boxes within tolerance, never requiring pixel equality. Arrange the named state and its dynamic values before comparing. Retain any stricter accepted measured/exact comparator and tolerance. Text matches require effective visible glyph paint and literal displayed control labels; password and other nondisplayed stored values never supply labels. Applied clips (except HTML elements inside the compared page or app surface whose computed `clip-path: inset(...)` or positioned `clip: rect(...)` collapses paint to empty area without masks or filters), masks, filters and unsupported text paint or native formatting leave visibility unproved and return an error. Arbitrary overlay occlusion and typography require separate verification.

For a Simulator Screen door, the comparator waits up to 10 seconds after page
load for its readiness protocol, app fonts and layout. It reads only the marked
same-origin iframe or open shadow app surface in local coordinates. It never
clicks Open or sends an action. Exit 6 (`screen-not-ready`) gives state, reason
and recovery guidance without a drawing table. An unopened app requires a
deliberate open, which can spend AI calls; a legacy viewer requires an update.
Keep a not-ready result distinct from a drawing mismatch and rerun after the
named prerequisite is satisfied. JSON has `drawing`, `url`, `outcome` (`not-ready`),
`code` (`screen-not-ready`), `state`, `reason`, `message` and `exit_code` (6),
without comparison `rows` or `passed`.

Verification must put a **Screen vs drawing** table in `verify.md` and in the body of the code PR (code space):

| Part | Drawing | Screen | Result |
|---|---|---|---|
| Named id or visible text | Expected state/region | Observed state/region | Pass or concrete failure |

Keep actual rows and the command's exit code. A missing/hidden part, wrong region or inverted order fails verify like a failing test. A missing browser, page or reference leaves verify unproved; never mark it passed. Return to build and compare again until the screen matches; never remove required parts from the reference to obtain a pass. A failing table remains a failure if workflow retry limits are reached. Include every linked reference state affected by the change. A 2048 screen without the drawing's score box, seed box or READY bar must fail even when behavior tests pass.

### App map

The Simulator has a **Screen** tab only when the repo has an app map: a JSON file that connects prompt operations to
screens. It holds no code. Without it, the person uses forms (or a terminal for `cli`).
- `pdd simulate` uses `app-map.json` at the repo root, else `app/app-map.json`. For another file:
  `pdd simulate <story> --app-map <path> --new`. Without `--new`, pdd reuses the open simulation and does not send the map.
  Git must show the file. It must be an app map like the one below, not a page of your app (`public/index.html`).
  pdd checks that the map is JSON with the app-map schema version and a name. A bad explicit map stops the command; a bad default map is skipped with a warning.
  Ordinary `pdd lint <story>` checks the Story's prompts and scenario (unless the scenario declares `"app_maps": ["app-map.json"]`); `pdd simulate <story> --new` checks `app-map.json` before starting Try.
- **A screen from an operation** (`"source": "operation"`): the operation draws the screen. `format` is `html`, `text`
  or `grid`. `result_pointer` selects the drawing: `/html` (a string) or `/lines` (a list of strings). `stylesheets` lists CSS files.
  The interpreter cleans the drawn html. It removes the `background` style, `list-style` and `aria-pressed`. Write
  `background-color` for a fill, `aria-current="true"` for a chosen button, and `display:block` on each `<li>` for a
  list with no bullets.
- **A screen from a mockup** (`"source": "mockup"`, `"operation": null`, `"format": "svg"`, `"result_pointer": null`):
  the screen prompt declares the screen and its callbacks in one code line, for example
  `@Composable fun MenuScreen(state: MenuState, onAdd: (String, String) -> Unit): Unit`. Its one operation gets
  `{"state": …}` and returns `{"svg": …}`. Its `## Appearance` section links the mockups:
  `![Menu with cart lines](views/menu-cart__phone.ui.svg)`. The `phase` in the screen input selects one
  (`"phase": "menu-cart"`), and the AI fills it. Each part to fill or tap has an `id`. The prose says how to fill each
  part and which callback a tap part gets ("region `price-latte-m`, callback `onAdd`, arguments `["latte","M"]`").
  This mockup-screen route reads all references selected from `Appearance` and `Appearance context`, with no
  four-view cap. The renderer enforces a 256 KiB safety cap per SVG and rejects scripts. The separate
  appearance-context reader selects at most four views with a 64 KiB total limit (section 16).
- `input` is the operation input, or the `state` of a mockup screen. `{"$ref": "/state/cart"}` copies a value (roots:
  `/state`, `/event`, `/result`, `/route`, `/world`). Other values are used as written. `state_schema` follows section 3.
- **A handler** connects a tap or a key to an operation. `match` may use `id`, `region_id`, `callback`, `href`,
  `value`, `name` and `label`. Examples: `button` `{"value": "place-order"}` (html `<button value="place-order">`),
  `region` `{"region_id": "price-latte-m", "callback": "onAdd"}` (SVG), `key` `{"value": "n"}`. `state` replaces the
  whole state: list every field, or give `null` to keep it.
- **`after`** runs follow-up operations in order on the same world before the screen redraws. Each step has exact keys
  `handler` (`{"prompt_path": "…", "operation": "…"}`), `input`, and `bind` (never top-level `prompt_path` or
  `operation` on the step; wrong step keys are refused as `invalid-after-step`). `after` `input` templates may copy
  values only from `/state` and the primary handler's `/result`; `bind` writes the whole typed `after` operation result
  to a non-root state pointer whose parent objects exist in `initial_state` and are required in `state_schema`.
- **`next`** always has these 3 keys. Stay on this screen: `{"kind": "same", "screen": null, "route_pointer": null}`.
  Go to a screen: `{"kind": "screen", "screen": "cart", "route_pointer": null}`. Use the router (only with a `router`):
  `{"kind": "route", "screen": null, "route_pointer": "/route"}`.
- **`/event`** in `input` or `state`: every event has `screen`, `target` and `kind`. `target` is the element's own
  `id` when that id is unique on the screen. A `link` adds `href`. A `key` or `command` adds `value` (the key). A
  `button` matched by `value` has that `value`. A `submit` (a `<form>`) adds `fields`: the form's named, visible
  fields, as strings (hidden inputs are not sent). A mockup `region` with a typed callback adds `arguments`. Use one
  field, for example `{"$ref": "/event/target"}`. The whole event (`{"$ref": "/event"}`) is refused.
- **Give every button a unique `id`** in the drawing. Then a tap keeps its target when the screen draws again, also a
  tap that waits in line.
- **On one screen, match all handlers of one kind by the same key.** Two `button` handlers with `{"value": …}` and
  `{"name": …}` on one screen are refused as `ambiguous-handler`.
- **A button on each row:** give the row buttons one `name` and the row's key as `id`:
  `<button name="mark-read" id="b2">Mark as read</button>`. One handler serves all rows:
  `{"kind": "button", "match": {"name": "mark-read"}, "input": {"id": {"$ref": "/event/target"}}, …}`. Then match the
  other buttons of that screen by `name` too (`name="show-all"`). The field that gets `/event/target` must be a plain
  `{"type": "string"}`: a stricter schema (`minLength`, `pattern`) is refused as `template-reference-schema`.
- Each tap costs the handler's AI calls plus 1 to draw the screen. In Harbor, opening cost 1 and a tap cost 2 to 3.
- A tap's worst case is the handler's worst case (section 10) plus 1 to draw. The Simulator allows 40 for each tap.
  A screen or handler whose prompt's worst case is over 40 never opens (refused at 0 calls). Keep the chain small.

A full, small app map (a book list with 2 filter buttons; one screen from an operation):
```json
{"schema_version": "prompt-runtime.app-map.v1", "name": "Bookshelf", "initial_screen": "shelf", "initial_route": null,
 "initial_state": {"show": "all", "books": [{"id": "b1", "title": "Dune", "read": false}]},
 "state_schema": {"type": "object", "properties": {
   "show": {"type": "string", "enum": ["all", "unread"]},
   "books": {"type": "array", "items": {"type": "object", "properties": {"id": {"type": "string"},
     "title": {"type": "string"}, "read": {"type": "boolean"}}, "required": ["id", "title", "read"],
     "additionalProperties": false}}},
   "required": ["show", "books"], "additionalProperties": false},
 "synthetic": true, "router": null, "routes": [], "stylesheets": [],
 "screens": [{"id": "shelf", "prompt_path": "prompts/shelf_page.prompt.md", "operation": "render", "source": "operation",
   "format": "html", "input": {"books": {"$ref": "/state/books"}, "show": {"$ref": "/state/show"}}, "result_pointer": "/html"}],
 "handlers": [
  {"screen": "shelf", "kind": "button", "match": {"value": "show-unread"},
   "handler": {"prompt_path": "prompts/books_api.prompt.md", "operation": "list_books"}, "input": {"read": "false"},
   "next": {"kind": "same", "screen": null, "route_pointer": null},
   "state": {"show": "unread", "books": {"$ref": "/result/books"}}},
  {"screen": "shelf", "kind": "button", "match": {"value": "show-all"},
   "handler": {"prompt_path": "prompts/books_api.prompt.md", "operation": "list_books"}, "input": {},
   "next": {"kind": "same", "screen": null, "route_pointer": null},
   "state": {"show": "all", "books": {"$ref": "/result/books"}}}]}
```
`render` returns `{"html": "…"}` with `<button id="show-unread" value="show-unread">Only unread</button>`.

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

Cut from the Harbor Coffee app map (`…` marks cut parts):
```json
{"schema_version": "prompt-runtime.app-map.v1", "name": "Harbor Coffee", "initial_screen": "menu", "initial_route": null,
 "initial_state": {"cart": [], …}, "state_schema": {…}, "synthetic": true, "router": null, "routes": [], "stylesheets": [],
 "screens": [{"id": "menu", "prompt_path": "prompts/menu_screen.prompt.md", "operation": null, "source": "mockup",
   "format": "svg", "input": {"phase": "menu-empty", "cart": {"$ref": "/state/cart"}, …}, "result_pointer": null},
   {"id": "cart", …the same, with "phase": "menu-cart"…}, …],
 "handlers": [{"screen": "*", "kind": "region", "match": {"region_id": "price-latte-m", "callback": "onAdd"},
   "handler": {"prompt_path": "prompts/cart.prompt.md", "operation": "add_item"},
   "input": {"cart": {"$ref": "/state/cart"}, "itemId": "latte", "size": "M"},
   "next": {"kind": "screen", "screen": "cart", "route_pointer": null},
   "state": {"cart": {"$ref": "/result/cart"}, …every other state field…}}, …]}
```

### Automatic Screen timers

The Runtime app-map contract supports host-scheduled Screen actions through the optional root `timers` array. The host schedules an action for the declared handler; it does not run JavaScript from the page. Keep requested timed game behavior in the app map and its operation. Script removal in section 20 does not mean timed Screen behavior is unsupported.

Each timer row has exactly `id`, `screen`, `interval_ms`, `enabled_pointer`, `generation_pointer`,
`handler`, `input`, `state` and `next`; `after` is optional. The map may have at most 16 timers.
IDs are unique and match `[A-Za-z0-9_-]{1,48}`. At most one timer may name each existing
non-wildcard screen. `interval_ms` is a strict integer from 1000 to 3600000. It sets a wait, not a
guaranteed tick rate. `enabled_pointer` selects a present, required Boolean state field with a valid
initial value. `generation_pointer` selects a present, required integer field from 0 through
9007199254740991, with a valid initial value. The handler must be an executable operation admitted
by the normal app-map rules.

The timer event has exactly `timer_id` (string), `generation`, `sequence` and `elapsed_ms` (integers
from 0 through 9007199254740991). A timer has no browser target. Its `input` can copy app state and
use only individually proved `/event/<field>` references. For example:

```json
"input": {
  "state": {"$ref": "/state"},
  "timer_id": {"$ref": "/event/timer_id"},
  "generation": {"$ref": "/event/generation"},
  "sequence": {"$ref": "/event/sequence"},
  "elapsed_ms": {"$ref": "/event/elapsed_ms"}
}
```

See the [Snake timer declaration](https://github.com/promptdriven/prompt-runtime/blob/main/prompts/examples/snake/app-map.json#L609-L675)
for a full map example and the [Runtime timer declaration](https://github.com/promptdriven/prompt-runtime/blob/main/prompts/prompt_runtime/program_app_map.prompt.md#L770-L798)
for admission rules. The [host scheduling contract](https://github.com/promptdriven/prompt-runtime/blob/main/prompts/server/web/screen_ticks.prompt.md)
waits for a live visible Screen and for ordinary or pending work to finish. It waits a fixed delay
after a completed action, submits one funded tick through the existing FIFO, and does not queue missed
ticks. Ticks use the existing action/call budget.

## 20. HTML checks and Simulator rendering

A structured HTML check selects a result string with `target: "result"` and a JSON Pointer such as `/html`.
Its `html` object names a selector and a kind. The selector matches a lowercase tag and optional exact attribute
values; it is not a CSS selector. For example:
```json
{"criterion_id": "AC1", "target": "result", "path": "/html", "op": "equals", "value": "Done",
 "html": {"selector": {"tag": "button", "attributes": {"id": "finish"}}, "kind": "text"}}
```
- `kind: "element"` supports `exists` only. Its boolean value defaults to `true`; `false` asserts no matches.
- `kind: "attribute"` also names `attribute`, such as `"attribute": "aria-current"`. It supports `exists`, `equals`,
  `not_equals`, `one_of` and `contains`.
- `kind: "text"` supports the same operations on concatenated descendant text, without whitespace normalization.
  Text `exists` tests for nonempty text; attribute `exists` tests presence. Both default to `true`.
  Other operations compare strings; `one_of` takes a list of strings and `contains` a nonempty substring.

Attribute and text assertions must hold for every matched element and fail if none match. A missing attribute
cannot satisfy `not_equals`. Raw HTML is validated before sanitization: at most 256 KiB of UTF-8 HTML, 4,096 elements,
64 nested non-void elements, 64 attributes per element, 64 selector attributes and 256 KiB of text. Duplicate
attributes, unmatched or misnested closing tags, closing tags for void elements, unclosed elements and unterminated
markup fail the check. Parser and size failures appear as `invalid_html` diagnostics.

**One rendering contract.** Structured HTML checks and the Simulator share the sanitizer. Checks select elements and read
attributes and text from the same sanitized HTML that the Simulator displays. The renderer derives interactive target markers
after sanitization. Reported attribute values describe the retained subset, with sensitive values redacted.
Assert only on elements, attributes and style declarations that survive. For dense grids, boards, or large tables (such as a 20×20 cell grid), return compact summary markup and key controls from simulated `render` and check structured state fields (`score`, positions, counts) in `pdd test`, rather than emitting hundreds of repeated HTML cell tags; verify full multi-hundred-cell DOM or canvas grids locally with `pdd test --screen URL --drawing SVG` or native browser tests in code space.

The supported HTML subset includes ordinary text and sections, headings, lists, tables, forms and controls.
Allowed attributes include `id`, `class`, `role`, `title`, form attributes such as `name`, `value`, `type` and `disabled`,
and accessibility attributes including `aria-label`, `aria-expanded`, `aria-checked`, `aria-selected` and `aria-current`.
Inline CSS supports physical and logical sizing (`width`, `height`, `inline-size`, `block-size` and their `min-`/`max-`
forms), `overflow-wrap`, `background-color`, color, borders, margin, padding, fonts, text, display, visibility,
opacity, overflow, flex and grid layout. Non-active `text-decoration` such as `line-through` survives.

The sanitizer removes `background` shorthand, `list-style`, `aria-pressed`, event handlers, unknown attributes and
CSS properties, scripts and active content. Embedded `<style>` elements are removed; admitted app stylesheets
provide stylesheet rules. External URLs are removed; retained URL attributes must be repository-local, without a
scheme, host or parent traversal. CSS URLs, scripts, unsafe functions and indirection such as `var()` are filtered.
Allowed CSS functions are `rgb`, `rgba`, `hsl`, `hsla`, `calc`, `min`, `max` and `clamp`, subject to the same safety
filters. A removed element, attribute or declaration cannot satisfy a structured HTML assertion. Script removal applies
to page content; it does not disable host-scheduled app-map timers (section 13). Do not infer that timed Screen behavior
is unsupported from this cleanup rule.

The all-Story check estimate includes entry executions, declared saved-data operations and nested prompt-call allowances; conditional operations can use fewer calls. The hard `--max-calls` cap stays authoritative. Named HTTP responses include `x-pdd-ai-calls`, `x-pdd-try-used`, `x-pdd-try-remaining`, `x-pdd-try-cap` and `x-pdd-usage-source` (`runtime` for a receipt, `last-known` for local zero-call responses). Startup shows session usage on stderr. Program stdout, HTTP bodies and status codes retain their program values; CLI stderr carries program text followed by accounting. No model call or repeat dispatch is made for accounting.
