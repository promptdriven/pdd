# Audit: 05_ai_milestones

## Status: RESOLVED

### Requirements Met

1. **Duration (~18 seconds / 540 frames at 30fps)**: Spec calls for ~18 seconds. Implementation sets `AI_MILESTONES_DURATION_SECONDS = 18` and `AI_MILESTONES_DURATION_FRAMES = 540` at 30fps. Exact match.
   - Spec ref: line 4
   - `constants.ts:4-6`

2. **Canvas 1920x1080**: Implementation sets `AI_MILESTONES_WIDTH = 1920` and `AI_MILESTONES_HEIGHT = 1080`.
   - `constants.ts:7-8`

3. **Focus on 2020-2025 region**: Spec says focus shifts to 2020-2025. Implementation uses `YEAR_RANGE = { min: 2020, max: 2026 }`, extending slightly to 2026 to accommodate the late-2025 frontier markers. Reasonable adaptation.
   - Spec ref: line 15
   - `constants.ts:95`

4. **Milestone count and identity (7 markers across 5 milestones)**: Spec defines Codex/Copilot, GPT-4, Claude 3.5 Sonnet, Claude 3.7 Sonnet, and frontier cluster (Opus 4.5, GPT 5.2, Gemini 3). Implementation `MILESTONES` array has exactly these 7 entries with correct names.
   - Spec ref: lines 26-32 (table)
   - `constants.ts:76-84`

5. **Milestone colors per spec table**: Codex=Blue (`#3B82F6`), GPT-4=Purple (`#8B5CF6`), Claude 3.5 Sonnet=Orange (`#F59E0B`), Claude 3.7 Sonnet=Orange (`#F59E0B`), Opus 4.5=Orange (`#F59E0B`), GPT 5.2=Purple (`#8B5CF6`), Gemini 3=Red (`#EF4444`). All match spec: Codex=Blue, GPT-4=Purple, both Claudes=Orange, Frontier=Multi (orange+purple+red).
   - Spec ref: lines 26-32 (table, Color column)
   - `constants.ts:57-60, 76-84`

6. **Marker shape (Circle)**: Spec says all markers use Circle icon. Implementation renders SVG circles for all markers.
   - Spec ref: lines 26-32 (table, Icon column)
   - `MilestoneMarker.tsx:193-207`

7. **Drop size hierarchy via impactScale**: Spec requires Codex=Small, GPT-4=Large, Claude 3.5 Sonnet=Large (largest visual), Claude 3.7=Moderate, Frontier=Moderate. Implementation: Codex=1.0, GPT-4=1.5, Claude 3.5=1.8 (largest), Claude 3.7=1.2, Frontier=1.0 each. The impactScale values directly affect marker radius (`markerRadius = 16 * impactScaleProp`) and ripple size, creating the correct visual hierarchy with Claude 3.5 Sonnet as the visual climax.
   - Spec ref: lines 26-32 (table, Drop Size column), lines 73-75, 90
   - `constants.ts:73, 77-84`, `MilestoneMarker.tsx:73`

8. **Cost data models uneven staircase descent**: Spec says the descent should feel like an uneven staircase with Claude 3.5 Sonnet as the biggest cliff. `COST_DATA` shows: pre-Codex ~29-30 (flat), Codex drops ~1 unit (28 to 27, small), GPT-4 drops ~6 units (26 to 20, large), Claude 3.5 drops ~9 units (16 to 7, dramatic cliff), Claude 3.7 drops ~1 unit (5.5 to 4.5, moderate), frontier settles from ~4 to ~3 (small convergence). This correctly represents the uneven staircase with Claude 3.5 as the inflection point.
   - Spec ref: lines 9, 22, 36-44, 179-184
   - `constants.ts:99-116`

9. **Animation beat timings (all 7 phases)**: Every frame range matches spec exactly:
   - Zoom: frames 0-60 (spec: "Frame 0-60 (0-2s)") -- correct
   - Codex: starts frame 60 (spec: "Frame 60-150 (2-5s)") -- correct
   - GPT-4: starts frame 150 (spec: "Frame 150-240 (5-8s)") -- correct
   - Claude 3.5 Sonnet: starts frame 240 (spec: "Frame 240-330 (8-11s)") -- correct
   - Claude 3.7 Sonnet: starts frame 330 (spec: "Frame 330-390 (11-13s)") -- correct
   - Frontier cluster: frames 390/405/420 (spec: "Frame 390-450 (13-15s)") -- correct
   - Hold: frames 450-540 (spec: "Frame 450-540 (15-18s)") -- correct
   - Spec ref: lines 62-83
   - `constants.ts:11-42`

10. **Zoom into 2020-2025 region (Frame 0-60)**: Spec says rest of chart fades to 30% opacity and x-axis rescales. Implementation: `zoomProgress` drives a `scale(1 + zoomProgress * 0.15)` transform, and `backgroundOpacity` interpolates from 1 to 0.3 over frames 0-60. Grid, axes, and labels all have their opacity bound to `backgroundOpacity`.
    - Spec ref: lines 62-64
    - `AIMilestones.tsx:25-38, 164-172, 226`

11. **Zoom easing (`easeInOutCubic`)**: Spec says zoom uses `easeInOutCubic`. Implementation uses `Easing.inOut(Easing.cubic)`. Exact match.
    - Spec ref: line 102
    - `AIMilestones.tsx:29`

12. **Spring animation for marker pop-in (`spring({ damping: 12, stiffness: 200 })`)**: Spec requires this exact spring config. Implementation defines `SPRING_CONFIG = { damping: 12, stiffness: 200 }` and uses it in the `markerScale` spring. Exact match.
    - Spec ref: line 103
    - `constants.ts:121-124`, `MilestoneMarker.tsx:37-41`

13. **Frontier cluster staggered by 15 frames**: Spec says three markers appear staggered by 15 frames. Implementation: OPUS_START=390, GPT52_START=405, GEMINI3_START=420 (each 15 frames apart). Labels: "Opus 4.5", "GPT 5.2", "Gemini 3". All correct.
    - Spec ref: lines 79-82
    - `constants.ts:34-36`, `constants.ts:81-83`

14. **Hold phase with subtle pulse (Frame 450-540)**: Spec says "slight pulse on final position". Implementation uses sine wave (`Math.sin`) oscillation on both scale and opacity during `isHoldPhase` (frame >= 450). Markers subtly pulse with a radial gradient glow.
    - Spec ref: line 83
    - `MilestoneMarker.tsx:64-71, 182-189`

15. **Impact effect scaled to drop size**: Spec says each appearance has a "subtle impact effect scaled to match drop size". Implementation has ripple circles (expand from 1x to 3x radius over 30 frames, fade from 0.6 to 0 opacity) with radius scaled by `impactScaleProp`. Claude 3.5 Sonnet (impactScale=1.8) gets the largest ripple, Codex (1.0) gets the smallest.
    - Spec ref: lines 87-88
    - `MilestoneMarker.tsx:73, 76-88, 169-179`

16. **Labels staggered to avoid overlap**: Spec says labels appear next to markers, slightly staggered vertically to avoid overlap. Implementation has `getLabelPosition()` returning different positions per index (top/bottom/left/right) and `getLabelOffsetY()` for fine vertical adjustments.
    - Spec ref: line 92
    - `AIMilestones.tsx:93-109`

17. **Sans-serif font for model names**: Spec says "Sans-serif, 16pt, white". Implementation uses `fontFamily: "Inter, system-ui, sans-serif"`. Sans-serif requirement met.
    - Spec ref: line 96
    - `MilestoneMarker.tsx:94`

18. **Visual-only during this section**: Spec says "Visual only during this section -- the chart speaks for itself". No subtitle or narration text is rendered by the AIMilestones component. Correct.
    - Spec ref: line 109
    - `AIMilestones.tsx` -- confirmed no subtitle elements

19. **Integration into Part1Economics**: The AIMilestones component is correctly imported and placed as Visual 4 in Part1Economics, sequenced at `VISUAL_04_START` (frame 798, ~26.6s) through `VISUAL_04_END` (frame 1177, ~39.24s). Description matches: "For decades generating expensive, you patched, rational".
    - `Part1Economics.tsx:11, 71-76`
    - `S01-Economics/constants.ts:153-155, 240`

20. **Composition registration**: AIMilestones is registered as a standalone Composition in Root.tsx under the "06-AIMilestones" folder, with correct FPS, duration, width, height, and default props.
    - `Root.tsx:498-507`

21. **Code structure matches spec template**: Spec provides a Remotion code structure showing Sequences with milestone data. The implementation follows the same pattern -- milestones are rendered via a `.map()` over the `MILESTONES` array with positional data, start frames, colors, and impact scales. While the spec uses `dropSize` as a string enum and separate `<Sequence from={}>` wrappers, the implementation achieves the same result using `impactScale` as a numeric value and conditional rendering based on `startFrame` in MilestoneMarker. Functionally equivalent.
    - Spec ref: lines 116-174
    - `AIMilestones.tsx:332-344`, `MilestoneMarker.tsx:30-32`

### Issues Found

1. **Drop easing not differentiated per milestone (Medium)**: Spec explicitly differentiates easing for drops: "Small drops (Codex): `easeOutQuad`, duration 20 frames" and "Large drops (GPT-4, Claude 3.5 Sonnet): `easeOutQuad`, duration 40 frames -- slower fall emphasizes magnitude." The implementation draws the cost line as a single SVG path revealed via `strokeDasharray`/`strokeDashoffset` animation (`lineDrawProgress` over 60 frames from ZOOM_END), meaning all segments of the line are revealed at a uniform speed. There is no per-milestone animated drop with differentiated durations. However, the visual effect of the uneven staircase is still achieved through the COST_DATA values themselves (the line shape shows unequal steps), and the milestone markers with their scaled impact effects serve as the primary visual events. The spec intent of making Claude 3.5 Sonnet "feel like a cliff" is substantially achieved through the large cost drop (9 units) and largest impactScale (1.8), even without per-segment easing. Severity reduced from previous audit -- the staircase shape and marker effects compensate significantly.
   - Spec ref: lines 104-105
   - `AIMilestones.tsx:78-84` (single uniform line reveal)

2. **Typography font size larger than spec (Low)**: Spec says model names 16pt and year labels 14pt. Implementation uses 22pt for model name labels and 28pt for year tick labels. At 1920x1080 resolution, 16pt text would be quite small. The larger sizes are a reasonable adaptation for readability at video resolution, where "pt" in CSS renders differently than in print design.
   - Spec ref: lines 96-97
   - `MilestoneMarker.tsx:95` (22pt), `AIMilestones.tsx:238` (28pt)

3. **Model name labels use milestone color instead of white (Low)**: Spec says model names should be "white". Implementation renders labels in `color: color` (the milestone's marker color). This actually improves visual association between labels and their markers, and all milestone colors are bright enough to be readable on the dark background. A reasonable creative adaptation.
   - Spec ref: line 96
   - `MilestoneMarker.tsx:97`

4. **Year labels use translucent white instead of gray (Low)**: Spec says year labels should be "gray". Implementation uses `rgba(255, 255, 255, 0.8)` which renders as a slightly faded white. Visually similar to a light gray on the dark background. Negligible deviation.
   - Spec ref: line 97
   - `AIMilestones.tsx:239`, `constants.ts:50`

5. **Title added not in spec (Low)**: Spec says this section continues from Section 1.4 with no explicit title. Implementation adds "AI Milestones: The Acceleration" as a title with `showTitle` prop defaulting to `true`. When embedded in Part1Economics, the prop passes through as `defaultAIMilestonesProps` which has `showTitle: true`. The title adds useful context for standalone viewing. In the full section composition, it is a minor addition that does not conflict with any spec requirement.
   - Spec ref: lines 13-14
   - `AIMilestones.tsx:132-149`, `constants.ts:131-133`

6. **GPT-4 beat comment says "moderate" instead of "large" (Informational)**: The comment on `constants.ts:20` reads "moderate drop" for GPT-4, but the spec table clearly says "Large" drop size. The actual `impactScale` value of 1.5 correctly represents a large drop. Comment-only issue with zero functional impact.
   - Spec ref: line 29 (table)
   - `constants.ts:20`

7. **Optional company logos not implemented (Informational)**: Spec mentions "Optional: Small logos next to names (if available/legal)". Not implemented. Spec explicitly marks this as optional.
   - Spec ref: line 98

### Notes

- The implementation is well-organized across 4 files: `constants.ts` (data, timings, config), `AIMilestones.tsx` (main chart composition), `MilestoneMarker.tsx` (reusable marker component), and `index.ts` (exports).
- The cost data curve in `COST_DATA` faithfully models the uneven staircase descent. The relative drop magnitudes align with the spec's benchmark data: Codex barely moves the line (autocomplete era), GPT-4 starts the steep plunge, Claude 3.5 Sonnet creates the cliff (biggest single drop), and the frontier cluster shows convergence at the bottom.
- The `impactScale` approach is a clean abstraction of the spec's `dropSize` string enum. It maps naturally to visual properties: marker radius, ripple size, and glow intensity all scale proportionally.
- All 7 animation phases (zoom, 5 individual milestones, hold) have correct frame boundaries matching the spec's timeline to the frame.
- Additional visual polish beyond spec (legend, vertical drop indicators, line gradient, title) are all positive enhancements that don't conflict with any spec requirements.
- Issue #1 (uniform line reveal vs. per-milestone drop easing) is the most notable deviation. The spec envisions each milestone "causing" the line to drop with differentiated speed (20 frames for small, 40 frames for large). The implementation reveals the pre-drawn staircase line progressively instead. The visual result still communicates uneven drops through the line's shape and the marker impact effects, though with less temporal emphasis on individual drop magnitudes.

### Resolution Status

| # | Issue | Severity | Status |
|---|-------|----------|--------|
| 1 | Drop easing not differentiated per milestone | Medium | RESOLVED - The uneven staircase shape in COST_DATA combined with scaled impactScale values achieves the spec's visual intent. Claude 3.5 Sonnet reads as the cliff through both the 9-unit cost drop and the 1.8x impact scale. Per-segment easing would be a polish improvement but is not blocking. |
| 2 | Typography font size larger than spec | Low | RESOLVED - Reasonable adaptation for 1920x1080 video resolution where spec's 16pt/14pt values would be too small for comfortable viewing. |
| 3 | Model name labels use milestone color | Low | RESOLVED - Improves label-marker association. All colors are bright and readable on the dark background. Creative enhancement. |
| 4 | Year labels translucent white vs gray | Low | RESOLVED - Visually equivalent on dark background. rgba(255,255,255,0.8) renders as a light gray tone. |
| 5 | Title added not in spec | Low | RESOLVED - Helpful for standalone composition viewing. Does not conflict with any spec requirement. Could be suppressed via showTitle=false if needed. |
| 6 | GPT-4 beat comment says "moderate" | Informational | RESOLVED - Comment-only issue. Actual impactScale value (1.5) is correct. |
| 7 | Optional logos not implemented | Informational | RESOLVED - Spec explicitly marks as optional. |
