# AUDIT S05 V1 -- CompoundCurves phase2

## Scene Metadata
- **Section**: Part 5 -- Compound Returns
- **Component**: CompoundCurves phase2 (Patching curve)
- **Time Range**: 2.7s - 23.6s
- **Frames Reviewed**: t=5.0s, t=15.0s, t=22.0s

## Script Visual Description
> "Patching curve: each patch = point of investment. Return is local. Curve grows linearly then flattens."

## Frame-by-Frame Observations

### Frame t=5.0s
- Full graph visible: Y-axis labeled "Cumulative Value of Investment", X-axis labeled "Time".
- Legend in top-left: "Patching" (orange) and "PDD" (blue).
- Orange Patching curve has started drawing with a sublinear (logarithmic/square-root) shape, rising steeply at first then starting to flatten.
- Two orange dots visible as "investment points" on the curve.
- PDD (blue) curve not yet visible.

### Frame t=15.0s
- Patching curve has extended across most of the graph, continuing its sublinear (flattening) trajectory.
- A dashed horizontal ceiling line is visible at the top, suggesting an asymptotic limit.
- Multiple orange dots (approximately 14) are placed along the curve as individual patch points.
- Annotations visible: "one bug fixed" near an early dot, "local return only" near a middle dot.
- PDD blue curve has just begun drawing at the very bottom-left origin area -- very small and close to the x-axis.

### Frame t=22.0s
- Nearly identical to t=15.0s. The patching curve extends further right, approaching the dashed ceiling line.
- More dots visible along the curve (approximately 17-18).
- Same annotations: "one bug fixed" and "local return only".
- The curve's flattening behavior is clearly visible -- it grows sublinearly, approaching but not exceeding the dashed limit.
- PDD blue curve still at the bottom, barely started.

## Compliance Assessment

| Criterion | Status | Notes |
|-----------|--------|-------|
| Patching curve visible | PASS | Orange curve clearly drawn |
| Each patch = point of investment | PASS | Orange dots mark individual patch investments |
| Return is local | PASS | "local return only" annotation present |
| Curve grows linearly then flattens | PASS | Curve grows sublinearly (concave down), approaching a dashed ceiling -- captures the "flattens" intent well |
| Axis labels correct | PASS | "Cumulative Value of Investment" (Y) and "Time" (X) |
| Legend present | PASS | Both "Patching" and "PDD" shown |

## Verdict: PASS
The patching curve behavior matches the script description well. The script says "grows linearly then flattens" -- the implementation shows a curve that rises steeply at first and then flattens toward a ceiling, which is arguably better than purely linear growth since it visually communicates diminishing returns more effectively. The "one bug fixed" and "local return only" annotations reinforce the narration about local returns. The orange dot investment points are clear and well-placed.

## Issues
- None significant. The curve shape is sublinear (concave down) rather than strictly "linear then flat", but this is a reasonable creative interpretation that communicates the same concept.
