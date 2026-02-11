# AUDIT S05 V2 -- CompoundCurves phase3

## Scene Metadata
- **Section**: Part 5 -- Compound Returns
- **Component**: CompoundCurves phase3 (Patching curve wobbles and dips)
- **Time Range**: 24.4s - 39.4s
- **Frames Reviewed**: t=26.0s, t=33.0s, t=38.0s

## Script Visual Description
> "Patching curve wobbles, dips. Annotations: 'new bug from patch', 'regression', 'merge conflict'"

## Frame-by-Frame Observations

### Frame t=26.0s
- Same graph as V1 but now the patching curve continues beyond the flattening zone and shows clear wobbles and dips.
- The curve rises, dips down, rises again, dips, creating an irregular jagged pattern in the upper portion.
- All three required annotations are visible with red/orange text and arrows pointing to dip locations:
  - "new bug from patch" -- pointing to a downward dip with an arrow
  - "regression" -- with a circular icon, pointing to another dip
  - "merge conflict" -- with an arrow, pointing to a third dip/wobble
- Earlier annotations ("one bug fixed", "local return only") remain visible.
- PDD blue curve still visible at the bottom-left, very small.

### Frame t=33.0s
- The graph has zoomed out slightly to show the full picture. Same wobbling/dipping behavior continues.
- All three annotations remain: "new bug from patch", "regression", "merge conflict".
- A callout box appears in the upper-right corner: "$1.52T annual US tech debt cost (CISQ)" -- this aligns with the narration mentioning the $1.52 trillion CISQ stat.
- The curve clearly shows sublinear growth with periodic dips -- visually communicating that patches create problems.

### Frame t=38.0s
- Similar view as t=33.0s. The $1.52T callout remains visible.
- Annotations still present. The wobbling patching curve is the dominant visual.
- PDD curve (blue) has begun to show more growth at bottom-left, starting to curve upward slightly.

## Compliance Assessment

| Criterion | Status | Notes |
|-----------|--------|-------|
| Curve wobbles | PASS | Clear irregular jagged pattern with ups and downs |
| Curve dips | PASS | Visible downward dips at annotated points |
| "new bug from patch" annotation | PASS | Present with arrow indicator |
| "regression" annotation | PASS | Present with circular icon |
| "merge conflict" annotation | PASS | Present with arrow indicator |
| Annotations at dip locations | PASS | Each annotation points to a specific dip/wobble |

## Verdict: PASS
Excellent execution of the script requirements. All three annotations are present and correctly positioned at curve dips. The wobbling behavior is clearly visible and communicates the instability of patching. The $1.52T CISQ callout is a bonus element that reinforces the narration about tech debt costs -- this is not in the script visual description but aligns with the narrated content about "$1.52 trillion."

## Issues
- None. This scene is a strong match to the script.
