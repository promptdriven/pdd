# Local screen comparison

Own `src/screen-compare.mjs`. Its module function `compareScreen({url, drawingPath, cwd, chromePath}, ports = {})` renders a real page and its `.ui.svg` reference in headless Chrome/Chromium, then returns `{drawing, url, viewport, rows, passed}`. `viewport` has CSS-pixel `width` and `height`. Each row has `{part, kind, expected, actual, status}`; `kind` is `id` or `text`, status is `pass`, `missing`, `hidden`, `region` or `order`. `expected` and `actual` are concise readable observations. `passed` is true only if every required row passes. The module function `formatScreenComparison(report)` returns a Markdown `Screen vs drawing` table and a pass/fail summary. Escape table pipes and line breaks from page content. No AI, PDD runtime, gh authentication or saved check batch is involved.

## Reference and browser

Resolve `drawingPath` from `cwd`; require a readable regular `.ui.svg` file. Accept only an http/https page URL without embedded credentials. A missing drawing, invalid SVG, unsafe reference, failed navigation or browser failure is an explicit error, never an empty passing comparison. Browser executable selection is explicit `chromePath`, then `PDD_CHROME_PATH`, then an installed Chrome/Chromium executable. `ports` may replace browser execution/environment for ordinary local tests. Do not require a private dependency or downloaded browser. Explain how to set `PDD_CHROME_PATH` when no browser exists.

Set the browser viewport from the drawing's positive viewBox width/height, falling back to positive numeric width/height when there is no viewBox. Reject a missing/invalid viewport; keep any nonzero viewBox origin accounted for in reference geometry. Render both the drawing and page with the same CSS-pixel viewport and device scale 1. Wait for page load and fonts, with a finite timeout; clean up the browser and temporary profile on success and every error. Read transformed bounding boxes from the rendered SVG, including nested groups and text, rather than assuming raw x/y attributes describe the screen. Never execute reference scripts or load external SVG resources; reject such reference content with a clear error.

## Comparison

Every visible reference id and every visible `<text>` label is required, including numeric labels and duplicates. Metadata (`title`, `desc`, `defs`), hidden elements and context-only subtrees (`data-context-only="true"` or class `context-only`) are excluded. The reference must contain at least one required part; malformed or unsupported reference content must not silently turn into a passing empty result.

An id maps to the page element with that exact unique id. Duplicate page/reference ids fail with a clear diagnostic. Text maps by exact whitespace-normalized visible text, preserving case, using the matched enclosing region where available. Consume distinct text occurrences once; a single label cannot satisfy repeated reference labels. Page text may be in ordinary DOM elements or form controls. A hidden label, accessibility name, script text or offscreen copy cannot satisfy a visible reference label. Visible means rendered, nontransparent, nonzero bounds and intersecting the viewport; report a matching hidden/outside element as `hidden` and an absent element as `missing`.

Compare matched parts' normalized center coordinates: each axis may differ by at most 0.15 of the viewport dimension. Outside this tolerance is `region`. Preserve the spatial order of nonnested parts whose reference bounds are separated vertically or horizontally by more than 2 CSS pixels; overlapping/nested parts impose no extra order. Compare visual geometry, never SVG source order or DOM/focus order. An inversion gives an `order` failure naming the other part. Presence is not enough: an id with unrelated content cannot hide missing text rows. A missing score box, seed box or READY bar must fail even if some score/seed words appear elsewhere.

Keep one table row per required id/text occurrence in stable reference order, including failed parts. State viewport and reference path in the report. This checks parts, text, approximate regions and order; it does not certify colors, typography or pixel equivalence. The caller must arrange the named reference state and dynamic values before invoking it; never drop unmatched words or numbers as “samples” to manufacture a pass.

## Dependencies

- [Screen rules](../../RUNBOOK.md#13-give-your-app-a-screen-app-map): generation and verification context. [Check](runtime-client.prompt.md) owns CLI routing, output and exit codes.
