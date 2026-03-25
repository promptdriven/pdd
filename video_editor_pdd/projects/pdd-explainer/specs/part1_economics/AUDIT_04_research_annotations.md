## Verdict
pass
## Summary
The frame is sampled at 90% progress (frame 1079/1200), which falls in the final hold phase (frame 960-1200). At this point, the spec requires all four annotations visible at balanced opacity with the chart. The frame shows three annotation cards stacked vertically along the right edge, but with several discrepancies from the spec:

1. **Annotation count and grouping**: The spec calls for four separate annotation cards (Individual task, Overall throughput, Code churn, Refactoring). The frame shows only three cards — Annotations 3 and 4 ('Code churn: +44%' and 'Refactoring: −60%') are merged into a single combined card. This deviates from the spec which defines them as distinct cards with separate callout lines and positions (center-right vs center-left).

2. **Card positioning**: All three cards are stacked on the right side of the frame. The spec places Annotation 4 ('Refactoring: −60%') at center-left, not right. The cards should be distributed around the chart, not all flush-right.

3. **Callout lines**: No visible callout lines connecting cards to their respective chart elements. The spec defines thin callout lines from each card to specific chart features (amber solid line, dashed line, debt area, debt gap edge).

4. **Annotation 1 color**: The header 'Individual task: −55%' appears in green (#4ADE80), which matches the spec. However the card border also appears green/teal rather than the specified #1E293B at 0.4 — it seems to use the annotation color for the border, which is a minor stylistic deviation.

5. **Annotation 2 extra text**: The 'Overall throughput: ~0%' card includes '+41% more bugs' as additional red text, which is not specified in the annotation card content. The fine print per spec should be '785 developers, one year'.

6. **Background and chart**: The dark navy-black background and chart with two lines (solid green dropping, dashed amber rising) are present and generally match. The debt shading area between the lines is visible.

7. **Chart lines are green/amber instead of both amber**: The solid line appears green rather than amber. The spec refers to a 'dropping solid amber line' — the rendered line color differs.
