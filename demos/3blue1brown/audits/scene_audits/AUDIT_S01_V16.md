# Scene Audit: S01 V16 - CrossingPoint (METR data)

**Section:** S01 Part 1 Economics
**Scene:** V16 - CrossingPoint (METR data - devs slower on large repos)
**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 249.76s - 279.02s (29.26s duration)
**Remotion component:** `remotion/src/remotion/08-CrossingPoint/CrossingPoint.tsx`
**Configuration:** `startAtFullView={true}` (no zoom animation)

---

## Verdict: NEEDS_FIX

---

## Frame Analysis

### Frame at t=250s (scene start)
- **Observed:** "The Economics of Code" chart is displayed at full view (no zoom animation, consistent with `startAtFullView=true`). All four data lines are visible: blue "Cost to Generate" descending steeply, amber baseline at ~10h, the forked small-codebase line dropping toward the bottom, the large-codebase fork staying flat at ~10-12h, the dashed amber "True cost (with tech debt)" line rising. The shaded tech-debt area between the large-codebase fork and the dashed total-cost line is visible. Legend is present in the upper right. No crossing-point marker or "We are here." label visible yet (CrossingPoint component starts at internal frame 0, marker appears at frame 90).
- **Expected per script:** "Focus on the upper fork. The large-codebase line stays flat at ~10-12 hours."
- **Assessment:** The chart structure is correct. The large-codebase line is visible and flat at ~10-12h as described. However, no annotations are present -- the METR data annotation is expected by the script at this point.

### Frame at t=265s (~15s into scene)
- **Observed:** The chart is identical in structure. The "We are here." label has appeared with its characteristic blue-bordered box and arrow pointing to the crossing point (around 2023-2024, ~11h). The white marker circle with blue glow is visible at the crossing point. Pulse rings have completed.
- **Expected per script:** "Small annotation: 'METR, 2025: experienced devs 19% slower on mature repos'. Then a second annotation fades in: 'Developers believed AI saved 20%. It cost 19%.'"
- **Assessment:** The "We are here." label and crossing-point marker are rendering correctly. However, the two METR data annotations specified in the script are completely absent from the rendered output.

### Frame at t=278s (~28s into scene)
- **Observed:** Identical to the t=265s frame. The chart, crossing-point marker, "We are here." label, and arrow are all stable in the hold phase. No additional annotations have appeared.
- **Expected per script:** Both METR annotations should be visible by this point. The narration at this timestamp discusses "a thirty-nine point gap."
- **Assessment:** Same issue as t=265s. No METR-related annotations are present.

---

## Discrepancies

### MAJOR: Missing METR data annotations (Known Issue - CONFIRMED)
- **Severity:** MAJOR
- **Description:** The script calls for two specific text annotations to appear during this scene:
  1. "METR, 2025: experienced devs 19% slower on mature repos"
  2. "Developers believed AI saved 20%. It cost 19%."
- **What is rendered:** Only the generic "We are here." label and crossing-point marker are shown. The CrossingPoint component (`CrossingPoint.tsx`) has no mechanism for per-segment annotations. The component only supports a fixed "We are here." label (lines 144-168) and an optional overlay text quote (lines 278-315, only shown when `showOverlayText=true`, which is not set for V16).
- **Root cause:** The CrossingPoint component is reused across multiple visuals (V7, V8, V9, V15, V16, V20) but has no parameterized annotation system. Each visual segment receives the same generic presentation. There is no prop or internal logic to display segment-specific annotations like the METR data.
- **Impact:** The narration discusses specific statistics ("nineteen percent slower," "twenty percent faster," "thirty-nine point gap") but the visual provides no supporting text. The viewer hears devastating data but sees only the generic chart with no anchoring labels. This is a significant gap between the audio and visual tracks.

### MINOR: Large-codebase line focus not emphasized
- **Severity:** MINOR
- **Description:** The script says "Focus on the upper fork" (the large-codebase line staying flat at ~10-12h). The current rendering shows all lines at their default opacities. The large-codebase fork is at 0.7 opacity and the small-codebase fork is at 0.35 opacity, which provides some visual hierarchy, but there is no dynamic highlighting, callout arrow, or dimming of other elements to draw attention specifically to the upper fork as the narration indicates.
- **Impact:** The viewer's eye is not specifically directed to the large-codebase line during the critical narration about METR data. The chart shows all lines with roughly equal visual weight.

---

## What Renders Correctly

1. **Chart structure:** All four data lines (blue generation cost, amber baseline, small/large codebase forks, dashed total cost) render correctly with proper axis labels, grid lines, and legend.
2. **Title:** "The Economics of Code" is correctly displayed.
3. **Crossing-point marker:** White circle with blue glow appears correctly at the intersection point (~2023.4, ~11.4h).
4. **"We are here." label:** Fades in with animation and positions correctly below-right of the crossing point, with arrow pointing to the marker.
5. **startAtFullView:** The chart correctly shows at full zoom with no zoom-in animation, as expected for a reprise usage of the component.
6. **Color scheme and legend:** Consistent dark theme with proper legend entries for all four line types.
7. **Tech-debt shaded area:** Amber-tinted region between the large-codebase immediate cost and total cost dashed line renders correctly.

---

## Recommendations

1. **Add annotation props to CrossingPoint:** Extend the component to accept an optional array of annotation objects (text, position, fade-in timing) so that per-segment annotations can be passed from the section composition. Example: `annotations?: Array<{ text: string; x: number; y: number; fadeInFrame: number; fadeOutFrame?: number }>`.
2. **Add V16-specific annotations in Part1Economics.tsx:** When rendering Visual 16, pass the two METR annotations as props to CrossingPoint:
   - Annotation 1 near the large-codebase line: "METR, 2025: experienced devs 19% slower on mature repos"
   - Annotation 2 fading in a few seconds later: "Developers believed AI saved 20%. It cost 19%."
3. **Consider highlighting the large-codebase fork:** During V16, dim or de-emphasize lines that are not the focus (the small-codebase fork and perhaps the dashed total-cost line) to draw attention to the upper fork as the script indicates.
