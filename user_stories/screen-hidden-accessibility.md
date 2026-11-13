# Compare a screen that has visually hidden accessibility text

As a developer who runs `pdd test --screen`, I want visually hidden accessibility elements on the page to be treated as hidden instead of unsupported clipping, so that screen-reader labels do not stop layout checks with exit code 5.

## Acceptance criteria

1. `pdd test --screen` on a 400 by 400 page with a visible `#search-box` region, visible "Search" heading and an unreferenced `.sr-only` HTML label styled with `clip-path: inset(50%)`, `clip: rect(0, 0, 0, 0)` on `position: absolute`, or both exits with code 0 and marks `#search-box` and "Search" as `pass`.
2. When the `.ui.svg` drawing requires a visible "Search query" label that exists on the page only inside a fully clipped `.sr-only` HTML element, `pdd test --screen` exits with code 1, marks "Search query" as `hidden` and sets `passed` to `false`.
3. When a page element uses partial or unestablished clipping such as `clip-path: inset(49%)`, `clip-path: circle(0)`, non-empty `clip: rect(0px, 1px, 1px, 0px)` or `clip: rect(0, 0, 0, 0)` on `position: static`, `pdd test --screen` exits with code 5 and prints the unsupported clipping error to stderr.
4. When a page element combines a collapsed clip with `filter` or `mask-image`, or when a `.ui.svg` drawing or Simulator Screen host or shell ancestor uses `clip-path` or `clip`, `pdd test --screen` rejects it with the existing error instead of passing.

## What must not change

- Visible regions, visible text, 15% center-position tolerance, spatial order and region-owned label matching stay the same.
- Ready Simulator Screen HTML and shadow surfaces treat fully clipped HTML accessibility elements inside the app surface as hidden while keeping host and shell clipping, masking and filter errors at exit code 5.

## Rules to check

- Treat an element on the compared page or selected app surface as hidden without setting the unsupported-visibility error only when every element in its effect chain is an HTML element inside that surface with `mask-image: none` and `filter: none`, and each effect element either has a collapsed `clip-path: inset(...)` (non-negative `%` or `px` insets with top+bottom `>= 100%` or left+right `>= 100%`) or has `position: absolute` or `fixed` with `clip: rect(...)` having numeric `bottom <= top` or `right <= left` (and `clip-path` either `none` or collapsed `inset(...)`). Forbidden: exit code 5 caused solely by such a fully clipped HTML accessibility element, or treating partial clipping, static `clip: rect(...)` without collapsed `clip-path`, SVG clipping, reference clipping, Screen host/shell clipping, masks or filters as hidden.
- A fully clipped HTML element and its descendants have `visible: false` and contribute no visible rendered text to enclosing elements. Forbidden: a required visible reference `<text>` label or `#id` receiving status `pass` from a fully clipped element, or hidden accessibility text concatenating into an enclosing visible element's label.
