# Compare a screen with a fully clipped accessibility label

As a person comparing a page with its drawing, I can still check the visible layout when the page includes a fully clipped accessibility label.

## Acceptance criteria

1. A 400 by 400 page with a visible box matching the drawing and an accessibility-only span styled with `width: 1px`, `height: 1px`, `clip-path: inset(50%)` and `overflow: hidden` completes the comparison; the visible box passes and the comparison passes.
2. Removing that span leaves the matching visible box passing. A fully clipped page label cannot satisfy a visible drawing label; it is reported hidden or missing and the comparison fails.
3. Applied clipping that leaves some paint visible or whose effect cannot be established does not become an automatic hidden exclusion or a pass: return an unsupported-visibility error when its visible parts cannot be established.
4. Masking, filters, text paint and unsupported reference geometry retain their existing visibility safeguards; an effect whose visible parts cannot be established produces an explicit error, not a passing comparison.

## Rules to check

Exclude an element and its contents only when their rendered paint is established to be completely clipped away. Continue comparing other visible parts. A clipping declaration, an accessibility class or role, or a small box by itself does not establish that result. Do not use the hidden exception to accept partially visible or uncertain clipping, unknown masking/filter effects, masked text as its underlying literal, or unsupported painted reference parts. Existing viewport, matching, geometry, order, output and error rules remain in force.

Forbidden results: exit 5 solely because of the fully clipped label in criterion 1; a passing visible-label row supplied by that label; or a pass produced by silently ignoring uncertain or partially visible paint.

## Scope

The first case comes from [issue 2934](https://github.com/promptdriven/pdd/issues/2934); the control and existing safeguards follow the prior screen comparison contract. The issue does not decide which of several drawing states to select or authorize ignoring arbitrary masked content. The caller still arranges the reference state.

Prompt tests: not run; no verdict. Browser rendering, page loading and local SVG effects have no faithful supported Runtime binding for this module. Native public browser/CLI cases must verify these criteria, including the issue case and control, a referenced fully clipped label, partial and uncertain clipping, and the existing mask, filter, text-paint and reference guards.
