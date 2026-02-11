# Scene Audit: S01 V15 - CrossingPoint (patch line forks)

**Section:** S01 Part 1 Economics
**Scene:** V15 - CrossingPoint (patch line forks)
**Time range:** 232.12s - 248.38s (16.26s duration)
**Remotion component:** `08-CrossingPoint/CrossingPoint.tsx` (with default props, `startAtFullView=false`)
**Auditor:** Claude Opus 4.6
**Date:** 2026-02-09

## Verdict: NEEDS_FIX

---

## Frame Analysis

### Frame at t=233s (local frame ~26, zoom-out phase)

**Observed:** The full "Economics of Code" chart is displayed mid-zoom-out. All four data series are visible:
- Blue "Cost to Generate" line descending from top-left to bottom-right
- Amber solid baseline (pre-fork 2015-2020)
- Amber solid fork lines diverging after 2020 (small codebase plunging, large codebase staying flat/rising)
- Amber dashed "True cost (with tech debt)" line rising

The chart is zoomed slightly (scale ~1.3x) and animating toward full view. The shaded tech-debt area between the large codebase and dashed lines is visible as a brown/amber fill. The legend in the upper right shows all four series: "Cost to Generate", "Patch (small codebase)", "Patch (large codebase)", "True cost (with tech debt)".

**Assessment:** The fork structure IS correctly rendered. The two amber paths diverge at 2020 as specified. However, there are no on-chart annotations labeling the fork paths (e.g., "Small codebase" / "Large codebase" near their respective lines). The legend in the corner provides these labels, but the script calls for direct annotations near the forking point.

### Frame at t=240s (local frame ~236, hold phase)

**Observed:** Chart is fully zoomed out. The "We are here." marker (white circle with blue glow) is visible near the second crossing point (~2023.4). An arrow points from the "We are here." label box to the crossing marker. All four lines and the tech-debt area are rendered. The legend remains in the upper right.

**Assessment:** The fork structure is visible and correct. However, the script specifies the annotation "Same tools. Different codebase sizes." which does NOT appear anywhere on screen. The "We are here." label is shown, but this is a CrossingPoint-specific feature for a different narrative moment (crossing point drama), not the V15 fork narrative about "two stories."

### Frame at t=247s (local frame ~446, beyond component duration)

**Observed:** Identical to t=240s. The composition has reached the end of its 300-frame internal timeline and holds its final state. "We are here." label, arrow, and crossing marker all remain visible. No additional annotations or text overlays.

**Assessment:** Static hold. Still missing fork annotations.

---

## Issue Summary

### ISSUE 1: Missing "Small codebase" / "Large codebase" on-chart annotations (MAJOR)

**Script requirement:** "The immediate patch cost line FORKS into two paths at 2020. Lower path labeled 'Small codebase' plunges down. Upper path labeled 'Large codebase' stays flat."

**What is rendered:** The fork IS structurally present in the chart data. The two amber lines diverge at 2020 correctly -- the small codebase line plunges toward ~1.5h by 2025, while the large codebase line stays flat at ~12h. However, these labels only appear in the corner legend (small text: "Patch (small codebase)" and "Patch (large codebase)"). There are no direct annotations ON or NEAR the fork lines themselves.

**Impact:** Without per-line labels near the fork point, viewers cannot quickly identify which fork represents which scenario. The legend is small and positioned in the corner, making it hard to associate with the diverging lines, especially at video playback speed. This is a known issue flagged in the section-level audit as "Per-segment annotations missing (known MAJOR design limitation)."

**Recommended fix:** Add animated text labels near each fork path. "Small codebase" should appear near the lower amber line around year 2022-2023. "Large codebase" should appear near the upper amber line in the same region. These could fade in during the zoom-out phase (frames 0-60) or shortly after.

### ISSUE 2: Missing "Same tools. Different codebase sizes." annotation (MAJOR)

**Script requirement:** 'Annotation: "Same tools. Different codebase sizes."'

**What is rendered:** No such text appears on screen at any point during this scene. The only text overlay is the "We are here." label from the CrossingPoint component, which is narrative context for the crossing point moment, not the fork narrative.

**Impact:** The annotation is a key conceptual takeaway for this scene -- it concisely explains WHY the fork matters. Its absence means the visual does not reinforce the narration's core message.

**Recommended fix:** Add a text annotation that fades in during this scene, positioned near the fork point (around year 2020 on the chart). Could be placed below the chart area or as a callout near the divergence point.

### ISSUE 3: "We are here." marker is potentially misleading in this scene context (MINOR)

**Script requirement:** The V15 scene's purpose is to show the fork and explain why patching is "two stories." The "We are here." marker with its crossing-point emphasis belongs to earlier scenes (V7/V8) and later scenes (V20).

**What is rendered:** The CrossingPoint component always shows its full animation sequence including the "We are here." label starting at frame 150. In this V15 context, the label appears before the narration has even reached the crossing-point discussion.

**Impact:** Minor -- the marker provides useful spatial reference. But it may draw attention away from the fork, which is the visual focus of this scene per the script.

**Recommended fix:** Consider adding a prop to CrossingPoint to suppress the "We are here." label and crossing marker when this component is used for the fork narrative (V15). Alternatively, accept this as a reasonable visual continuity choice.

### ISSUE 4: Zoom-out animation may be redundant (MINOR)

**Script requirement:** "Return to the chart." implies a cut or transition back to a familiar chart, not necessarily a zoom animation.

**What is rendered:** Because `startAtFullView=false`, the first 2 seconds play a zoom-out animation from a zoomed-in perspective. This is the same zoom-out that plays in V7. By V15, viewers have seen this chart multiple times, so re-playing the zoom-out may feel repetitive rather than adding visual interest.

**Impact:** Minor. The zoom-out takes 2 seconds of a 16-second scene, and the narration starts immediately at "This is why AI-assisted patching is really two stories." The chart is zoomed in during those opening words rather than showing the full fork.

**Recommended fix:** Consider using `startAtFullView={true}` for V15 (as is done for V8, V9, V16) so the chart appears immediately at full view, letting the fork be visible from the first frame of the scene.

---

## What Works Well

1. **Fork data structure is correct.** The chart data accurately represents two diverging paths at 2020: small codebase dropping to ~1.5h, large codebase flat/rising to ~12h.
2. **Visual clarity of the fork.** The two amber lines are visually distinguishable -- the small codebase fork is rendered at 35% opacity while the large codebase fork is at 70% opacity, creating a clear hierarchy.
3. **Legend is present.** All four data series are labeled in the legend, even if on-chart annotations are missing.
4. **Tech-debt shaded area.** The amber fill between the large codebase line and the dashed total cost line effectively communicates the debt differential.
5. **Color palette and typography.** Consistent with the 3Blue1Brown aesthetic -- dark background, clean lines, readable text.

---

## Files Examined

- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/08-CrossingPoint/CrossingPoint.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/08-CrossingPoint/CodeCostChart.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/08-CrossingPoint/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/Part1Economics.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S01-Economics/constants.ts`
