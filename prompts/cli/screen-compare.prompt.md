# Local screen comparison

Own `src/screen-compare.mjs`. Its module function `compareScreen({url, drawingPath, cwd, chromePath, look = false}, ports = {})` renders a real page and its `.ui.svg` reference in headless Chrome/Chromium, then returns `{drawing, url, viewport, rows, passed}` (plus `look: true` when `look` is true). `viewport` has CSS-pixel `width` and `height`. Each row has `{part, kind, expected, actual, status}`; `kind` is `id`, `text` or (only when `look` is true) `look`, status is `pass`, `missing`, `hidden`, `region`, `order` or (only when `look` is true) `look`. `expected` and `actual` are concise readable observations. `passed` is true only if every required row passes. The module function `formatScreenComparison(report)` returns a Markdown `Screen vs drawing` table and a pass/fail summary. Render supplied content literally: escape Markdown backslashes, punctuation and HTML-special characters, and flatten line breaks so content cannot alter the table or introduce links/HTML. No AI, PDD runtime, gh authentication or saved check batch is involved.

## Reference and browser

Resolve `drawingPath` from `cwd`; require a readable regular `.ui.svg` file. Accept only an http/https page URL without embedded credentials. A missing drawing, invalid SVG, unsafe reference, failed navigation or browser failure is an explicit error, never an empty passing comparison. Ignore valid XML comments and treat CDATA as literal text; reject malformed or nested comments rather than removing delimiters and reinterpreting their contents. Browser executable selection is explicit `chromePath`, then `PDD_CHROME_PATH`, then an installed Chrome/Chromium executable. `ports` may replace browser execution/environment for ordinary local tests. Do not require a private dependency or downloaded browser. Explain how to set `PDD_CHROME_PATH` when no browser exists.

Set the browser viewport from the drawing's positive viewBox width/height, falling back to positive numeric width/height when there is no viewBox. Reject a missing/invalid viewport; keep any nonzero viewBox origin accounted for in reference geometry. Render both the drawing and page with the same CSS-pixel viewport and device scale 1. Wait for page load and fonts, with a finite timeout; clean up the browser and temporary profile on success and every error. Start the browser with a mock keychain and a basic password store, so a fresh temporary profile never reads the operating system keychain; on macOS, Chrome otherwise asks for its "Chrome Safe Storage" item at every start. Read transformed bounding boxes from the rendered SVG, including nested groups and text, rather than assuming raw x/y attributes describe the screen. Never execute reference scripts or load external SVG resources; reject such reference content with a clear error.

## Comparison

Every visible reference id and every visible `<text>` label is required, including numeric labels and duplicates. Metadata (`title`, `desc`, `defs`), hidden elements and context-only subtrees (`data-context-only="true"` or class `context-only`) are excluded. The reference must contain at least one required part; malformed or unsupported reference content must not silently turn into a passing empty result.

An id maps to the page element with that exact unique id. Duplicate page/reference ids fail with a clear diagnostic. Text maps by exact whitespace-normalized visible text, preserving case. When a reference label has a uniquely matched enclosing id, only that page element's own text or descendant occurrences may satisfy it. If none exist there, report `missing`, even when the same label appears elsewhere; never fall back to outside text. Without a matched enclosing id, text matching remains global. Consume distinct text occurrences once; a single label cannot satisfy repeated reference labels. Page text may be in ordinary DOM elements or form controls. Only literal displayed control labels count: text-like input values, textarea values, selected option labels and explicit button/submit/reset labels. Password secrets and checkbox/radio, color, range, image, file or hidden input values are not visible labels. Native date/month/week/time/datetime-local values may be formatted; their stored strings must not be assumed displayed. A native control may satisfy its visible id without supplying a literal text match. Never include private input values in reports or diagnostics.

A hidden label, accessibility name, script text or offscreen copy cannot satisfy a visible reference label. Visible means rendered, effective nontransparent paint, nonzero bounds and intersecting the viewport; report a matching hidden/outside element as `hidden` and an absent element as `missing`. Text visibility follows effective glyph paint, including text-fill overrides, rather than CSS color alone; the same rule applies when text supplies an id's only paint. Masked text cannot supply its underlying literal. If text stroke/shadow, masking, formatted native controls or applied clipping/filter effects cannot be established, return an explicit unsupported-visibility error rather than a pass. Ordinary visible text (including SVG textPath ids), safe local SVG gradient paint and structural regions with visible painted descendants remain supported. Distinguish structural SVG containers and unapplied resource/metadata nodes from unsupported painted elements. If nontransparent paint or geometry cannot be established, including stroked SVG geometry with zero width or height in its geometric bounds, return an explicit unsupported-visibility error; never silently omit that required reference id or accept an unsupported page element as its match. Apply this guard after hidden/transparent exclusion so those reference parts stay excluded.

Compare matched parts' normalized center coordinates: each axis may differ by at most 0.15 of the viewport dimension. Outside this tolerance is `region`. Preserve the spatial order of nonnested parts whose reference bounds are separated vertically or horizontally by more than 2 CSS pixels; overlapping/nested parts impose no extra order. Compare visual geometry, never SVG source order or DOM/focus order. An inversion gives an `order` failure naming the other part. Presence is not enough: an id with unrelated content cannot hide missing text rows. A missing score box, seed box or READY bar must fail even if some score/seed words appear elsewhere.

Keep one table row per required id/text occurrence in stable reference order, including failed parts. State viewport and reference path in the report. Without `look`, this checks parts, text, approximate regions and order; it does not certify colors, typography or pixel equivalence. The caller must arrange the named reference state and dynamic values before invoking it; never drop unmatched words or numbers as “samples” to manufacture a pass.

## Optional look check

When `look` is true, also capture rendered canvas and painted box surfaces from both the reference SVG and the selected page/app surface, and append the `kind: "look"` rows returned by [screen design check](screen-design-check.prompt.md) (`evaluateScreenLook`). Without `look`, retain exact existing return keys, row kinds and summary wording.

Capture look facts in reference-viewport CSS pixels:

- **Reference `canvasColor`:** the effective RGB `[r, g, b]` fill of the first non-excluded, non-text visible SVG shape covering at least 85% of both viewport dimensions, or `null` when the drawing leaves its backdrop unpainted (for local gradients, use the first visible stop color).
- **Page `canvasColor`:** the topmost nontransparent background RGB `[r, g, b]` across the app root (`host` for shadow doors, else `documentElement`/`body`) and any single visible non-text child covering at least 85% of both app-viewport dimensions (such as `<main>` or root `<svg>`), defaulting to `[255, 255, 255]` when the browser canvas is left transparent.
- **Reference `boxes`:** in reference order, each visible required `id` part whose bounds are at least `24 × 16` CSS pixels and smaller than 85% of at least one viewport axis, and whose own SVG shape (or single non-text painted child shape covering at least 70% of both group axes) has a nontransparent fill distinct from `canvasColor` (RGB distance `> 12`) or a visible stroke (`strokeWidth > 0`). Record `{id, box, fill, stroke}`.
- **Page `boxes`:** for each page element with an `id`, record `{id, visible, painted, box, fill, stroke}` using the element itself (or, when the `#id` wrapper has no own paint and wraps a single visible child element covering at least 80% of both axes, that child surface). `painted` is true only when the surface has a nontransparent fill/background distinct from the page `canvasColor` (RGB distance `> 12`), or a visible border/outline/SVG stroke; descendant text alone never sets `painted` true.

When `report.look` is true (or `report.rows` contains `kind: "look"`), `formatScreenComparison(report)` ends with `Parts, text, regions, order and look within tolerance; pixel equivalence is not required.` instead of the parts-only disclaimer.

## Supported Simulator Screen doors

This section defines behavioral refinement for issue 3038 under the reviewed
Screen readiness Story. Existing reference, visibility, label ownership, geometry,
ordering, input and execution-error rules remain required within the selected app
surface.

This section fully defines the public wire format and consumer interpretation.
Compatible producers must supply it; producer prompts own when and how they
publish it.

Recognize the versioned Screen door by `data-pdd-screen-door="1"` on the top-level
`document.documentElement`.
A recognized door must not fall back to comparing its shell. Ordinary pages
continue to use their top-level document; do not recursively search unrelated
iframes, nested frames or arbitrary shadow roots.

After successful page load, start one 10,000 ms monotonic readiness deadline,
including app fonts and layout settling. Elapsed time greater than or equal to
10,000 ms is timeout; readiness must complete strictly before that boundary.
This is inside the existing 60,000 ms
whole-browser limit, not an extension or a reset of it. Observe the root's
`data-pdd-screen-state` and the selected app surface without activating controls
or issuing app actions. `loading` waits; `not-open` and `error` stop immediately.
Busy actions stay loading; an unknown action result is an error even when an
older frame remains painted. An observed ready surface must still be current
when captured. Never convert an expired readiness deadline to a drawing mismatch.
An earlier browser/navigation/execution failure keeps its existing error category.

| Observation | `state` | `reason` in the not-ready error |
| --- | --- | --- |
| Readiness or app settling has not completed by the deadline | Last valid `loading` or `ready` | `timeout` |
| Initial open is required | `not-open` | `not-open` |
| Door publishes error | `error` | Its `data-pdd-screen-reason`: `state-read-failed`, `render-failed` or `action-unknown` |
| Unsupported protocol version, missing/invalid state, or invalid error reason | `unknown` | `viewer-update-required` |
| Ready without exactly one usable selected app surface | `ready` | `surface-unavailable` |
| Legacy door without version 1 | `unknown` | `viewer-update-required` |

Legacy identification requires the existing inert shell fingerprint together:
root `data-try-session`, a `<base>` whose resolved path is `/__pdd/screen/`, and
a same-origin `door-screen.js` script resolved beneath that prefix. Root door
identity with any unsupported version also requires a viewer update. Do not
identify doors from status words, page title, URL alone or a lone iframe.

The producer marks exactly one current iframe `data-pdd-app-frame="html"`, or
one current open shadow host `data-pdd-app-frame="shadow"`, beneath `#frame`.
Inspect only that iframe's same-origin content document or that host's open
shadow root. Exclude shell labels, ids, status, buttons and all other documents.
An inaccessible, detached, missing or ambiguous marked surface is unavailable,
not an empty app. Wait for that document's fonts and two animation frames within
the readiness deadline, then recheck door state and surface identity before
capturing. Do not bypass cross-origin isolation or change app state.

Use the app's own CSS-pixel viewport for visibility and normalized centers:
iframe content-window viewport for HTML; marked host's local content area for
SVG/text/grid. Translate shell offsets out, account for renderer scaling, and
normalize each axis by the selected app viewport's positive width/height. The
reference remains measured at its drawing viewport. Shell chrome height, padding
and page scroll must not move app parts into different regions or make app text
satisfy a label. Report viewport continues to describe the drawing viewport.
Preserve actual app visibility, unsupported-visibility errors, occurrence identity,
label ownership, unique ids, region tolerance and order checks. Ready app
mismatches retain their ordinary failed rows.

A not-ready outcome throws an Error with `code: "screen-not-ready"`, `exitCode: 6`,
`state` and `reason` from the table, plus an actionable plain `message`. It returns
no comparison report and no missing-part rows. `not-open` explains that the person
must deliberately open the app before rerunning and that opening can spend AI
calls. `viewer-update-required` names the Screen viewer update prerequisite;
`timeout` names the 10-second ready wait; unknown-action guidance requests
read-only reconciliation, never another automatic send. Never click Open, key,
submit, invoke app targets, send POST, or spend model calls to make a comparison
ready. Existing action lookup/recovery belongs to the door, not this module.

## Dependencies

- [Screen design check](screen-design-check.prompt.md): required generation/runtime/verification context for optional `look` surface evaluation.
- [Screen rules](../../skills/pdd-prompting/runbook/screens-and-svg.md#13-give-your-app-a-screen-app-map): required packaged generation and verification context for drawing fidelity and local screen comparison. Its other links are navigation-only for this module's wire contract.

## Caller navigation

[Check](runtime-client.prompt.md) owns CLI routing, output and exit codes.
