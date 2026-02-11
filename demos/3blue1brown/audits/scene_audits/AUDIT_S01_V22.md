# Scene Audit: S01_V22 - PieChart (Software Cost Breakdown)

**Section:** S01 Part 1 Economics
**Scene:** V22 - PieChart
**Video:** `part1_economics.mp4`
**Time range:** 394.82s - 420.36s (25.54s duration)
**Remotion component:** `remotion/src/remotion/12-PieChart/`
**Audit date:** 2026-02-09

---

## Verdict: PASS

---

## Frame-by-Frame Analysis

### Frame 1: t=396s (early in scene, ~1.2s after scene start)
- **Title:** "Where Software Costs Go" -- white, bold, centered at top. Clearly readable.
- **Pie chart base:** Circle outline is visible (subtle gray stroke on dark background).
- **Blue slice:** A small blue (cornflower blue, #4A90D9) segment is visible in the upper-right of the pie, spanning approximately 54 degrees from the 12 o'clock position. This correctly represents the "Initial Development" portion.
- **Label:** "Initial Development" label appears in white text to the upper right of the pie, connected by a thin connector line from the slice edge. No percentage shown yet at this point.
- **Maintenance slice:** Not yet drawn -- the rest of the pie is empty (just the outline circle). This matches the animation timing: the blue segment draws from frames 120-180, and amber starts at frame 180.
- **Assessment:** Correct. The animation is in its early stage, showing only the initial development slice as it should per the beat timing.

### Frame 2: t=405s (~10.2s into scene)
- **Title:** "Where Software Costs Go" -- still present, fully opaque.
- **Pie chart:** Fully drawn. Both slices are visible:
  - **Blue slice (Initial Development):** Small wedge in the upper-right, visually representing roughly 10-20% of the pie. The proportional size is correct.
  - **Amber/orange slice (Maintenance):** Large slice filling the remaining ~85% of the pie. Color is warm amber/orange (#D9944A).
- **Labels:**
  - "Initial Development" with "10-20%" in blue text, positioned outside the pie to the upper right with a connector line.
  - "Maintenance" with "80-90%" in amber text, positioned inside the large amber slice.
- **Percentage values:** Both "10-20%" and "80-90%" are clearly visible, matching the script description exactly.
- **Assessment:** Correct. The complete pie chart with all labels and percentages is displayed, matching the script's specification of "Initial Development: 10-20%" and "Maintenance: 80-90%".

### Frame 3: t=418s (~23.2s into scene, near end)
- **Title:** "Where Software Costs Go" -- still present.
- **Pie chart:** Identical composition to t=405s. Both slices fully drawn.
- **Labels:** All labels and percentages still visible and readable:
  - "Initial Development" / "10-20%"
  - "Maintenance" / "80-90%"
- **Visual quality:** Clean, no artifacts. The chart is holding steady in its final state (this is within the "hold with subtle pulse" phase, frames 360-450).
- **Assessment:** Correct. The chart maintains its final state clearly through the end of the scene.

---

## Verification Checklist

| Criteria | Status | Notes |
|----------|--------|-------|
| Title text matches script | PASS | "Where Software Costs Go" present and readable |
| Pie chart materializes (animation) | PASS | Circle outline -> blue slice -> amber slice progression confirmed |
| "Initial Development" label | PASS | Present with correct text |
| "10-20%" percentage | PASS | Present in blue color, matches script |
| "Maintenance" label | PASS | Present with correct text |
| "80-90%" percentage | PASS | Present in amber color, matches script |
| Proportional slice sizes correct | PASS | Blue ~15% of area, amber ~85% -- visually accurate |
| Color scheme (3B1B style dark bg) | PASS | Dark navy background (#1a1a2e), blue/amber contrast |
| Labels readable against background | PASS | White labels with text shadow, percentage in slice colors |
| Animation timing appropriate for narration | PASS | Chart builds during "80-90% of software cost" narration |
| No visual artifacts or glitches | PASS | Clean rendering throughout |
| Connector line for small slice | PASS | Thin line connects blue slice to its external label |

---

## Script Alignment

**Script visual description:** "Pie chart materializes. 'Initial Development: 10-20%'. 'Maintenance: 80-90%'."

**Actual rendering:** The pie chart materializes with a staged animation (outline -> blue slice -> amber slice -> percentages). Both labels and percentages match the script exactly. The visual emphasis correctly falls on the massive maintenance slice, reinforcing the narration about 80-90% of costs going to maintenance.

**Script narration alignment:** The narration discusses "eighty to ninety percent of software cost isn't building the initial system. It's maintaining it." The visual directly supports this with the dramatically disproportionate slice sizes.

---

## Component Source Review

- Component path: `remotion/src/remotion/12-PieChart/` (note: directory is `12-PieChart`, not `11-PieChart` as listed in assignment)
- Constants correctly define segments: initialDevelopment at 0-54 degrees (15% of 360), maintenance at 54-360 degrees (85% of 360)
- Percentage labels hardcoded as "10-20%" and "80-90%" matching script
- Animation beats well-structured: base circle -> blue segment -> amber segment -> percentages -> pulse hold

---

## Summary

The PieChart scene renders correctly and matches the script in all aspects. The animation progresses logically from an empty circle outline to the complete pie chart with labels and percentages. The data values ("Initial Development: 10-20%" and "Maintenance: 80-90%") are accurate. The visual design is clean, readable, and appropriately styled for a 3Blue1Brown-inspired presentation. No fixes are needed.
