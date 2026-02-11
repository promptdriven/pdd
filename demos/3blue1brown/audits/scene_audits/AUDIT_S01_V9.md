# Scene Audit: S01 V9 - CrossingPoint (Third Appearance - GitClear Data)

**Section:** S01 Part 1 Economics
**Scene:** V9 - CrossingPoint (third appearance)
**Video:** `outputs/sections/part1_economics.mp4`
**Time range:** 119.14s - 139.1s (19.96s duration)
**Audited frames:** t=120s, t=130s, t=138s
**Component:** `remotion/src/remotion/08-CrossingPoint/CrossingPoint.tsx`
**Props:** `startAtFullView={true}` (all other defaults)

---

## Verdict: NEEDS_FIX

---

## Script Requirements vs. Rendered Output

### Narration (script)
> "And GitClear confirmed it across two hundred eleven million lines of code. Since AI coding assistants arrived, code churn is up forty-four percent... Meanwhile, refactoring collapsed by sixty percent."

### Expected Visuals (script)
> "New annotation materializes: 'Code churn: +44% (GitClear, 2025, 211M lines analyzed)' pointing to the debt area. Another: 'Refactoring: -60%' pointing to the widening gap."

---

## Frame-by-Frame Analysis

### Frame at t=120s (scene entry, ~0.86s into V9)
- **Observed:** The "Economics of Code" chart is displayed at full view (no zoom animation, consistent with `startAtFullView={true}`). All four data lines are visible: blue "Cost to Generate" declining steeply, amber solid baselines (small and large codebase forks), and amber dashed "True cost (with tech debt)" rising. The shaded tech debt area is rendered between the large codebase immediate and total cost lines. The legend is visible in the upper-right corner. No annotations are present on the chart. No "We are here." marker is visible yet (it appears at local frame 150+, which is 5s into the segment, i.e., ~124s video time).
- **Assessment:** Chart is correct and fully rendered. However, the GitClear annotations that should be materializing are absent.

### Frame at t=130s (~10.86s into V9)
- **Observed:** The chart now shows the "We are here." label with its glowing blue-bordered tooltip and arrow pointing to the second crossing point (where blue line crosses below the large codebase immediate cost). The pulsing marker and radial burst effects have completed. The chart is otherwise static. No GitClear-specific annotations ("+44% code churn", "-60% refactoring") are visible anywhere on the screen.
- **Assessment:** The "We are here." marker display is working correctly. The segment-specific annotations called for by the script are completely missing.

### Frame at t=138s (~18.86s into V9, near end)
- **Observed:** Identical to t=130s. The "We are here." label and arrow remain. No additional annotations have appeared. The scene is in its hold phase.
- **Assessment:** No change. The annotations never materialize during this entire 20-second segment.

---

## Issues Found

### ISSUE 1: Missing GitClear Annotation "+44% Code Churn" [MAJOR - Known]
- **Severity:** MAJOR
- **Category:** Missing visual element
- **Description:** The script calls for an annotation reading "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" to materialize and point to the tech debt area of the chart. This annotation is completely absent from the rendered output.
- **Root cause:** The `CrossingPoint` component has no mechanism for per-segment annotations. It renders the same visual regardless of which narration segment it accompanies. The component only supports `showTitle`, `showOverlayText`, and `startAtFullView` props -- none of which provide annotation functionality. Visual 8 (GitHub data) and Visual 9 (GitClear data) both receive identical `CrossingPoint` instances with `startAtFullView={true}` and no distinguishing configuration.
- **Status:** Known design limitation (documented in assignment).
- **Impact:** The viewer hears specific statistics ("+44% churn", "211M lines") but sees a generic chart with no corresponding visual reinforcement. This violates the 3Blue1Brown principle that narration and visuals should be tightly synchronized.

### ISSUE 2: Missing Refactoring Annotation "-60%" [MAJOR - Known]
- **Severity:** MAJOR
- **Category:** Missing visual element
- **Description:** The script calls for a second annotation reading "Refactoring: -60%" pointing to the widening gap between the lines. This is also completely absent.
- **Root cause:** Same as Issue 1 -- the component has no annotation mechanism.
- **Status:** Known design limitation (documented in assignment).
- **Impact:** Same as Issue 1. The narration specifically says "refactoring collapsed by sixty percent" while the visual shows nothing corresponding to this claim.

### ISSUE 3: No Visual Differentiation from V8 [MODERATE]
- **Severity:** MODERATE
- **Category:** Design gap
- **Description:** Visual 8 (GitHub/Uplevel data, 79.16s-118.08s) and Visual 9 (GitClear data, 119.14s-139.1s) render identically. Both use `CrossingPoint` with `startAtFullView={true}` and no other differentiating props. Since V9 creates a new Sequence (local frame resets to 0), the "We are here." label and marker animate in again from scratch, providing the only visible change -- a re-animation of the same elements. The viewer has no visual cue that the data source or statistic being cited has changed.
- **Suggested fix:** Add segment-specific annotation props to `CrossingPoint` (e.g., an `annotations` array) or create a wrapper component (`CrossingPointAnnotated`) that overlays text callouts on top of the base chart. Each V7/V8/V9 instance should display the statistics relevant to its narration segment.

---

## What IS Working

1. **Chart rendering:** The "Economics of Code" chart renders correctly with all four line types, proper colors, grid, axes, and labels.
2. **Full view mode:** `startAtFullView={true}` correctly skips the zoom-out animation, presenting the chart immediately at full scale.
3. **Tech debt area:** The shaded amber area between large codebase immediate and total cost lines is properly rendered, visually representing the "debt" that the narration references.
4. **"We are here." marker:** The crossing point marker, pulse effect, arrow, and label all animate correctly and are positioned at the second crossing point.
5. **Legend:** All four line types are labeled in the legend (Cost to Generate, Patch small/large codebase, True cost with tech debt).
6. **Timing:** V9 starts at the correct narration beat (119.14s, coinciding with segment [34] about GitClear).

---

## Recommendations

1. **Add annotation support to CrossingPoint.** Introduce an optional `annotations` prop (array of `{text, pointTo: 'debt_area'|'gap'|'crossing', delay: number}`) so each segment instance can display context-specific statistics.
2. **For V9 specifically**, two annotations should animate in sequentially:
   - At ~2s local: "Code churn: +44% (GitClear, 2025, 211M lines analyzed)" with a leader line pointing to the tech debt shaded area.
   - At ~12s local: "Refactoring: -60%" with a leader line pointing to the widening gap between the immediate cost (large codebase) and total cost lines.
3. **Consider also adding annotations for V8** (GitHub/Uplevel data) to differentiate it visually from V7 and V9.
