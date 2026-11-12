# Compare the app only after its Screen is ready

As a person checking a Simulator Screen against its drawing, I want the actual app to be ready before a drawing verdict, so that loading or setup requirements do not look like missing app parts.

## Acceptance criteria

1. A Simulator Screen that becomes ready before the 10-second readiness deadline is compared inside its actual app surface, after its fonts and layout settle, within the existing 60-second browser limit.
2. A Simulator Screen still loading at that deadline exits 6 with code screen-not-ready, state loading and reason timeout, without a drawing table or missing-part verdict.
3. An unopened Simulator Screen exits 6 with state not-open and reason not-open, and explains that I must deliberately open it before rerunning because opening can spend AI calls.
4. A failed state read, failed render or unknown action exits 6 with state error and the corresponding reason state-read-failed, render-failed or action-unknown; an older painted frame cannot turn pending or unknown work into ready.
5. Ready HTML, SVG, text and grid Screens use only their declared app surface, with positions measured from the app area; shell labels, duplicate ids and shell offsets cannot affect the app verdict.
6. A missing required part inside a ready app still exits 1 with the failed drawing rows; a matching ready app exits 0. Existing label ownership, visibility, region and order checks stay required.
7. A legacy or unsupported Simulator viewer exits 6 with state unknown and reason viewer-update-required; a ready viewer with a missing, ambiguous or inaccessible app surface exits 6 with state ready and reason surface-unavailable.
8. Ordinary pages keep their existing pass, mismatch, invalid-input and browser/navigation-error behavior. Comparison never clicks Open or app controls, sends an action, or spends model calls.
9. In JSON mode, a not-ready result has drawing, url, outcome not-ready, code screen-not-ready, state, reason, message and exit_code 6, with no rows or passed field; ordinary comparison JSON stays unchanged.

## Scope

The nine acceptance criteria were approved in chat.

The comparator owns readiness consumption and app-local capture. The CLI routing
owner preserves its outcome. The paired Runtime Story owns readiness publication
and renderer commit. Ordinary reference and visibility rules remain required.
No broad recursive frame discovery, initial-open automation or app verification
framework is included.

## Evidence and verification plan

The original author's Snake input is unavailable. Its hosted reproduction remains
NOT REPRODUCED. Controlled native fixtures establish the independently observed
comparator defect; they do not claim the original hosted outcome.

Run `PDD_CHROME_PATH=/usr/local/bin/chromium node --test test/screen-door-readiness.test.mjs`
from the repository root. The self-contained test serves isolated synthetic
Screen protocol pages and invokes the actual `node bin/pdd.mjs test --screen`
process. It checks app DOM capture, exact stdout/exit and zero action POSTs.
The executable native cases are in that test runner.
Retain ordinary screen comparison and label ownership regressions as well.

Runtime prompt check: Not run. The comparator has no Runtime interface or
faithful registered binding for browser execution. Do not add a result oracle,
reduce its broad contract to a pure projection, or label native browser tests
an interpreter scenario. Native browser proof and independent contract review
are required. No before-fail/after-pass interpreter verdict is claimed.
