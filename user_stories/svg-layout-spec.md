# Keep linked screen drawings structurally safe and aligned

As a screen author, I want local SVG lint to validate my linked `.ui.svg` drawing links, XML safety, and `viewBox` geometry offline without false alarms from English prose, while browser comparison verifies the rendered screen against the drawing.

## Acceptance criteria

1. Running `pdd lint` on a screen prompt linking a valid, inert `.ui.svg` with a finite sane `viewBox` emits 0 SVG warnings and exits with code 0, without AI or network calls.
2. Linking a missing, wrong-case, symlinked, unsafe (`<script>`, `on*`, external `href`/`url()`), malformed-XML, or bad-`viewBox` (non-finite, zero/negative, hairline, or extreme aspect ratio `> 50`) `.ui.svg` produces a deterministic `Warning: SVG layout <prompt> -> <drawing>: ...` advisory.
3. Plain Markdown `.ui.svg` links outside `## Dependencies` without image syntax `![label](...)` warn that scoped uploads skip them.
4. Browser comparison (`pdd test --screen`) renders the real page at the drawing viewport and fails when a required visible text occurrence or id is missing, hidden, in the wrong region, or out of spatial order.

## What must not change

- SVG layout warnings remain advisory, use 0 AI or network calls locally, and honor `pdd-workspace.json` path filtering and strict no-symlink reads.
