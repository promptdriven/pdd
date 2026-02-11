# Scene Audit: S01 V7 - CrossingPoint (First Appearance)

## Status: NEEDS_FIX

## Scene Details
- **Section:** S01 Part 1 Economics
- **Visual Slot:** V7 (CrossingPoint, first appearance)
- **Video:** `outputs/sections/part1_economics.mp4`
- **Time range:** 62.96s - 78.08s (15.12s duration)
- **Frames examined:** t=64s, t=70s, t=77s
- **Remotion component:** `remotion/src/remotion/08-CrossingPoint/`
- **Spec file:** `specs/01-economics/07_crossing_point.md`

## Script Requirements

**Visual description:** "Camera pulls back. As the immediate line drops, the shaded debt area EXPANDS upward. The dashed 'total cost' line at the top barely moves. The gap between what you feel and what's real becomes visible."

**Narration:** "But watch the dashed line. The total cost. It's barely moving. Because even though each patch is faster, every patch still leaves residue. Technical debt. And that debt accumulates -- faster now, because you're patching faster."

## Internal Frame Mapping
- CrossingPoint component starts at global frame 1889 (62.96s)
- t=64s -> internal frame ~31 (zoom-out phase, frames 0-60)
- t=70s -> internal frame ~211 (hold phase, frames 210-300)
- t=77s -> internal frame ~421 (past 300-frame design, all clamped to final state)

## Frame-by-Frame Analysis

### Frame 1: t=64s (internal frame ~31, zoom-out phase)
- **Chart visible:** Yes. Full chart is present with all four data series rendered.
- **Blue "Cost to Generate" line:** Visible, starting at ~32h (2015) and dropping steeply to ~3h (2025). Correctly blue.
- **Amber "Patch (small codebase)" line:** Visible at lower opacity (faded), forking from the baseline at 2020 and dropping. Correct.
- **Amber "Patch (large codebase)" line:** Visible at medium opacity, forking at 2020 and staying flat/slightly rising to ~12h. Correct.
- **Amber dashed "True cost (with tech debt)" line:** Visible, rising from ~22h to ~33h. Correctly dashed. Correct.
- **Shaded debt area:** Present as a large amber-tinted region between the large codebase immediate line and the dashed total cost line from 2020 onward. Correctly shows the expanding gap.
- **Zoom animation:** The frame is partway through the zoom-out. The chart appears slightly zoomed in (scale ~1.25 based on the interpolation at frame 31). Y-axis label "Developer hours per module" is partially clipped at left edge.
- **Legend:** Present in upper-right corner showing all four line types. Correct labels and styling.
- **Title:** "The Economics of Code" is shown at top center. Correct.
- **Crossing markers:** Not yet visible (first crossing appears at frame 60). Correct for this timing.

**Issues at t=64s:**
1. Y-axis label is partially clipped during zoom-out phase (minor -- only visible for first ~2 seconds).

### Frame 2: t=70s (internal frame ~211, hold phase start)
- **Full chart:** Fully zoomed out, all axes and labels visible including "Developer hours per module" on Y-axis.
- **First crossing marker:** Visible as a white circle with blue glow at the intersection of the blue generate line and the amber dashed total cost line (~2022, ~27h). Correct position.
- **Second crossing marker:** Visible as a larger white circle with blue glow and concentric pulse rings at the intersection of the blue generate line and the amber solid large-codebase line (~2023.4, ~11.4h). Correct position. Pulse rings are visible as faint concentric circles around the marker.
- **"We are here." label:** Visible below and to the right of the second crossing marker. White text on dark translucent background with blue border. Period included. Arrow pointing from label to crossing marker is visible. All correct.
- **Shaded debt area:** Clearly visible as the large amber region expanding between the large codebase immediate line and the dashed total cost line. Visually communicates "the gap between what you feel and what's real."
- **All chart lines:** Visible with correct styling (blue solid for generate, amber solid at different opacities for patch lines, amber dashed for total cost).

**Issues at t=70s:**
None significant. The chart, markers, label, and debt visualization are all working correctly.

### Frame 3: t=77s (internal frame ~421, well past hold phase)
- **Visual state:** Nearly identical to t=70s frame. All elements are in their final state.
- **Continued pulsing:** Subtle pulse rings are visible around the second crossing marker, confirming the "continued pulsing" during the hold phase works correctly.
- **All elements stable:** Chart, markers, label, arrow, legend, title all remain visible and correctly positioned.

**Issues at t=77s:**
None. The composition holds correctly in its final state.

## Alignment with Script Narration

The script says:

1. **"Camera pulls back"** -- PARTIAL MATCH. The zoom-out animation plays from frames 0-60 (first 2 seconds of the scene, 62.96s-64.96s). By t=64s it is mid-zoom. The viewer does see the camera pulling back, though the transition is brief.

2. **"As the immediate line drops, the shaded debt area EXPANDS upward"** -- MISMATCH. The script describes a dynamic animation where the immediate line visibly drops while the debt area expands. In the actual rendering, the chart is static -- all data is drawn at once. There is no progressive reveal of the lines or the debt area expanding. The chart simply appears fully formed (with the zoom-out being the only animation). The "expanding upward" debt area is present as a visual but does not animate/expand during this scene.

3. **"The dashed 'total cost' line at the top barely moves"** -- PARTIAL MATCH. The dashed line is clearly visible and rises gently from ~22h to ~33h. However, because there is no progressive/animated line drawing, the viewer cannot see that it "barely moves" in contrast to something else moving -- it is static from the start.

4. **"The gap between what you feel and what's real becomes visible"** -- PARTIAL MATCH. The shaded debt area does visualize this gap, but it does not "become" visible dynamically. It is present from the beginning of the scene.

## Known Design Limitation (from Section-Level Audit)

**MAJOR: Per-segment annotations are MISSING.** The CrossingPoint component shows the same generic chart for all its segments (V7, V8, V9, V15, V16, V17, V20). The only differentiation is:
- V7: plays zoom-out animation (default props)
- V8, V9, V16, V17: `startAtFullView={true}` (skip zoom)
- V20: `showOverlayText={true}` (narration overlay)

For V7 specifically, the narration describes watching the dashed line and debt accumulation, but the component does not highlight or annotate these elements. The viewer sees the full chart with all crossing markers and "We are here." label, which is forward-looking content that does not match this narration segment. The spec's animation sequence (zoom out -> first crossing -> second crossing -> label) plays in the first 7 seconds (internal frames 0-210), but V7 runs for 15.12 seconds, meaning the last 8 seconds are the same hold view.

## Issues Summary

### MAJOR Issues

1. **No progressive line/debt animation matching narration (Severity: HIGH)**
   - **Script says:** "As the immediate line drops, the shaded debt area EXPANDS upward"
   - **Actual:** Chart lines and shaded area are static; they do not animate or reveal progressively. The debt area is fully rendered from the first frame after zoom-out.
   - **Impact:** The narration describes a dynamic cause-and-effect that the viewer cannot see. The visual storytelling of "watch the dashed line" and "the gap becomes visible" requires temporal progression that is absent.
   - **This is part of the known MAJOR design limitation:** the CrossingPoint component was built as a single composition showing the full dramatic crossing (with "We are here." as the payoff), but it is reused for narration segments that describe different aspects of the chart. V7's narration is about debt accumulation, but the visual jumps ahead to the crossing-point climax.

2. **Premature crossing markers and "We are here." label (Severity: MEDIUM)**
   - At V7's narration, the script describes watching the dashed line and debt. But the component's internal animation plays the full sequence: by t=70s (7 seconds into V7), both crossing markers and the "We are here." label are visible. This content corresponds to the spec's narration ("But look where we are now. The cost to generate...") which maps to V20, not V7.
   - The viewer sees the climactic "We are here." reveal during narration about debt accumulation, which creates a disconnect. The narration says "watch the dashed line" while the visual is already showing the dramatic conclusion.

### MINOR Issues

3. **Y-axis label clipping during zoom-out (Severity: LOW)**
   - At t=64s (during zoom-out), the Y-axis label "Developer hours per module" is partially cut off at the left edge. This resolves once zoom-out completes at ~65s. Purely cosmetic and transient.

4. **15.12s duration vs 10s component design (Severity: LOW)**
   - The CrossingPoint component is designed for 300 frames (10s), but V7 runs for 15.12s. The extra 5.12s shows the final hold state with no additional animation. The component handles this gracefully via interpolation clamping, but it means 5+ seconds of static visuals while narration is still playing.

## What Works Well

- **Chart data accuracy:** All four data series (generate, small codebase patch, large codebase patch, total cost with debt) are correctly plotted with the right values.
- **Visual hierarchy:** The blue generate line is visually prominent (thicker stroke), patch lines use amber coloring with differential opacity, and the dashed total cost line is clearly distinguished.
- **Shaded debt area:** The amber-tinted region between the large-codebase immediate cost and total cost effectively communicates the concept of hidden technical debt.
- **Legend:** Clear and correctly labeled, positioned out of the way of the data.
- **Crossing markers:** Both first and second crossing markers are correctly positioned at the mathematically computed intersection points.
- **"We are here." label:** White text, bold, 28pt, period included, blue-bordered pill with arrow -- all match spec.
- **Zoom-out animation:** Smooth easeOutCubic transition from zoomed view to full chart view.

## Recommendation

The core problem for V7 is a structural one already identified in the section-level audit: the CrossingPoint component is a single 10-second composition that plays its full dramatic arc regardless of which narration segment it accompanies. For V7, this means:

1. The narration focuses on debt accumulation ("watch the dashed line"), but the visual races ahead to show the crossing point climax.
2. There is no progressive animation of lines or the debt area expanding to match the narration's descriptive language.

To properly fix this, the CrossingPoint component would need per-segment behavior -- for example, a `phase` or `segment` prop that controls which elements are visible and animated. For V7 specifically, the component should:
- Show the chart lines being drawn progressively
- Animate the debt area expanding upward
- Highlight/pulse the dashed total cost line when the narrator says "watch the dashed line"
- NOT show the crossing markers or "We are here." label (save those for V20)

This is consistent with the known MAJOR design limitation flagged in the section-level audit.
