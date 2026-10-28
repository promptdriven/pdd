# Keep the screen aligned with its drawing

I can use my linked screen drawing as the layout spec and see which required parts the prompt or built screen misses.

## Acceptance criteria

1. A linked `.ui.svg` defines the screen's visible parts, words, spatial order, ids and named state; the prompt and drawing name the same parts, and build reads the drawing and rebuilds until they match.
2. Local SVG lint warns about controls only in the prompt, labels only in the drawing and drawn regions whose layout the prompt never specifies, without AI/network calls or a warning-only failure exit.
3. Existing complete server lint includes the same local drawing warnings and preserves its server requests, admission, rows and exit behavior.
4. A browser comparison renders the real page at the drawing viewport and fails when a required visible text occurrence or id is missing, hidden, in the wrong region or out of spatial order.
5. Verify records the real Screen vs drawing table in the code PR; missing parts or unavailable browser evidence cannot pass verify.

## Expected cases

| Case | Expected result |
|---|---|
| 2048-like prompt names four direction buttons absent from its drawing | Local warnings name the missing directional controls. |
| Drawing has READY and score/seed boxes; prose mentions score/seed data only | Warnings name READY and unspecified score/seed layout regions; never claim the words score/seed are wholly absent. |
| No runtime tests or interface, but a Git-visible prompt links a drawing | Unselected `check --lint --local` still inspects it; no auth or runtime state is needed. |
| Prompt explicitly declares every drawn label and region and shows each named control | No SVG mismatch warnings. |
| Metadata title/desc, hidden and context-only drawing parts | They create no required visible parts. |
| Reference has transformed groups, repeated labels or entity-encoded text | Use rendered geometry, decoded text and distinct visible occurrences. |
| Page has every part and label within the reference regions and order | Comparison exit 0 with passing table rows. |
| Page lacks score/seed box ids and READY text, even though score/seed words appear elsewhere | Comparison exit 1 with explicit missing rows; behavior tests cannot waive it. |
| Matching ids/text are hidden, outside the viewport, moved beyond 15% or swapped | Comparison exit 1 with hidden/region/order evidence. |
| Drawing/browser is missing, URL fails, viewport is invalid or required reference set is empty | Nonzero diagnostic; never an empty passing table. |
| Invalid local/screen option combination | Exit 2 before auth, browser launch or runtime calls. |

These expected cases precede implementation. Ordinary Node unit tests cover the local modules/CLI; no live AI checks or prompt approvals are part of this change.
