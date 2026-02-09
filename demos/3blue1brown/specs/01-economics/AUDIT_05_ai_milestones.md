# Audit: 05_ai_milestones

## Status: ISSUES FOUND

### Requirements Met

1. **Duration**: Spec calls for ~18 seconds. Implementation sets `AI_MILESTONES_DURATION_SECONDS = 18` at 30fps = 540 frames. Matches exactly. (`constants.ts:5-6`)

2. **Milestone Count and Identity**: Spec defines 7 markers across 5 milestones (Codex/Copilot, GPT-4, Claude 3.5 Sonnet, Claude 3.7 Sonnet, then frontier cluster of Opus 4.5 / GPT 5.2 / Gemini 3). Implementation `MILESTONES` array has exactly these 7 entries. (`constants.ts:76-84`)

3. **Milestone Colors**: Spec table: Codex=Blue, GPT-4=Purple, Claude 3.5=Orange, Claude 3.7=Orange, Frontier=Multi. Implementation: Codex=`#3B82F6` (blue), GPT-4=`#8B5CF6` (purple), Claude 3.5=`#F59E0B` (orange/amber), Claude 3.7=`#F59E0B` (orange/amber), Opus 4.5=`#F59E0B` (orange), GPT 5.2=`#8B5CF6` (purple), Gemini 3=`#EF4444` (red). All correct. (`constants.ts:57-60, 76-84`)

4. **Drop Size Hierarchy via impactScale**: Spec requires Codex=Small, GPT-4=Large, Claude 3.5=Large (largest visual impact), Claude 3.7=Moderate, Frontier=Moderate/Small. Implementation: Codex=1.0, GPT-4=1.5, Claude 3.5=1.8, Claude 3.7=1.2, Frontier markers=1.0 each. This correctly creates the uneven staircase with Claude 3.5 Sonnet as the visual climax. (`constants.ts:77-84`)

5. **Cost Data Staircase**: Spec says drops should be uneven with Claude 3.5 Sonnet being the biggest cliff. COST_DATA shows: Codex drops from ~29 to ~28 (small, 1 unit), GPT-4 drops from ~26 to ~20 (large, 6 units), Claude 3.5 drops from ~16 to ~7 (dramatic, 9 units), Claude 3.7 drops from ~5.5 to ~4.5 (moderate, 1 unit), frontier settles from ~4 to ~3 (small). The cost data correctly models the uneven staircase. (`constants.ts:99-116`)

6. **Animation Beat Timings**: All frame ranges match spec exactly:
   - Zoom: frames 0-60 (spec: Frame 0-60) -- correct
   - Codex: starts frame 60 (spec: Frame 60-150) -- correct
   - GPT-4: starts frame 150 (spec: Frame 150-240) -- correct
   - Claude 3.5: starts frame 240 (spec: Frame 240-330) -- correct
   - Claude 3.7: starts frame 330 (spec: Frame 330-390) -- correct
   - Frontier cluster: frames 390, 405, 420 (spec: staggered by 15 frames) -- correct
   - Hold: frames 450-540 (spec: Frame 450-540) -- correct
   (`constants.ts:11-42`)

7. **Zoom Behavior**: Spec says zoom into 2020-2025 region with rest of chart fading to 30% opacity. Implementation uses `scale(1 + zoomProgress * 0.15)` with `easeInOutCubic` easing and fades background elements to opacity 0.3. Matches spec. (`AIMilestones.tsx:25-38`)

8. **Zoom Easing**: Spec says `easeInOutCubic`. Implementation uses `Easing.inOut(Easing.cubic)`. Correct. (`AIMilestones.tsx:29`)

9. **Spring Animation for Markers**: Spec says `spring({ damping: 12, stiffness: 200 })`. Implementation uses `SPRING_CONFIG = { damping: 12, stiffness: 200 }`. Correct. (`constants.ts:121-124`, `MilestoneMarker.tsx:37-41`)

10. **Frontier Cluster Stagger**: Spec says 3 markers staggered by 15 frames (390, 405, 420). Implementation: OPUS_START=390, GPT52_START=405, GEMINI3_START=420. Correct. (`constants.ts:34-36`)

11. **Label Anti-Overlap**: Spec says labels should be staggered to avoid overlap. Implementation has `getLabelPosition()` returning different positions per index (top/bottom/left/right) and `getLabelOffsetY()` for fine-tuning. Well implemented. (`AIMilestones.tsx:93-109`)

12. **Hold Phase Pulse**: Spec says "slight pulse on final position" during frames 450-540. Implementation has `isHoldPhase` sine wave pulse on markers during hold. Correct. (`MilestoneMarker.tsx:64-71`)

13. **Impact Ripple Effect**: Spec says each appearance has a subtle "impact" effect scaled to match drop size. Implementation has ripple circles that expand and fade over 30 frames, with radius scaled by `impactScaleProp`. Correct. (`MilestoneMarker.tsx:76-88, 169-179`)

14. **Visual Only During Hold (No Subtitle)**: Spec says "Visual only during this section - the chart speaks for itself". Previous audit noted a subtitle "Each release accelerated the decline" was removed. Confirmed: no subtitle text exists in current code. Correct. (`AIMilestones.tsx:402-405` -- only closing tags, no subtitle)

15. **Year Range**: Spec says focus on 2020-2025 region. Implementation uses `YEAR_RANGE = { min: 2020, max: 2026 }`. Close enough (extends to 2026 to accommodate late-2025 markers). Correct. (`constants.ts:95`)

16. **Marker Shape**: Spec table says all markers use "Circle" icon. Implementation renders circles. Correct. (`MilestoneMarker.tsx:193-207`)

17. **Integration into Part1Economics**: The AIMilestones component is correctly sequenced as Visual 4 in the Part1Economics orchestration, appearing at `VISUAL_04_START` (frame 798, ~26.6s into the section). (`Part1Economics.tsx:72-76`, `S01-Economics/constants.ts:153-155`)

18. **Vertical Drop Indicators**: Not in spec, but implementation adds dashed vertical lines from markers to x-axis as a visual enhancement. Good addition. (`MilestoneMarker.tsx:210-219`)

19. **Line Gradient**: Not in spec, but implementation uses a gradient from `COLORS.LINE_COST` to `#60A5FA` for the cost line. Nice visual polish. (`AIMilestones.tsx:302-305`)

20. **Legend**: Not in spec, but implementation adds a legend that fades in after the frontier cluster. Good addition. (`AIMilestones.tsx:347-401`)

### Issues Found

1. **Drop Easing Not Implemented (Medium)**: Spec calls for differentiated easing on drops: "Small drops (Codex): `easeOutQuad`, duration 20 frames" and "Large drops (GPT-4, Claude 3.5 Sonnet): `easeOutQuad`, duration 40 frames -- slower fall emphasizes magnitude." The implementation does not apply `easeOutQuad` easing to the line drops at all. The cost line is drawn as a single stroke-dasharray animation (`AIMilestones.tsx:78-84`) that reveals uniformly, rather than animating individual drop segments with different durations. The spec explicitly differentiates drop durations (20 frames for small, 40 frames for large) to emphasize magnitude visually. This is the most significant missing piece.
   - **Spec reference**: Lines 104-105
   - **Implementation**: `AIMilestones.tsx:78-84` -- single uniform line reveal

2. **Typography Size Mismatch (Low)**: Spec says model names should be 16pt and year labels 14pt. Implementation uses 22pt for model name labels (`MilestoneMarker.tsx:95`) and 28pt for year tick labels (`AIMilestones.tsx:238`). These are significantly larger than spec. However, given 1920x1080 rendering resolution, the larger sizes may be a reasonable adaptation for readability.
   - **Spec reference**: Lines 96-97
   - **Implementation**: `MilestoneMarker.tsx:95`, `AIMilestones.tsx:238`

3. **Label Color Mismatch (Low)**: Spec says model names should be white and year labels gray. Implementation renders model name labels in the milestone's own color rather than white (`MilestoneMarker.tsx:97` -- `color: color`), and year labels in `rgba(255, 255, 255, 0.8)` (translucent white) rather than explicit gray (`AIMilestones.tsx:239`). The colored labels arguably improve readability by associating labels with their markers, but deviate from spec.
   - **Spec reference**: Lines 96-97
   - **Implementation**: `MilestoneMarker.tsx:97`, `AIMilestones.tsx:239`

4. **Title Not In Spec (Low)**: Spec says this section continues from Section 1.4 with no explicit title. Implementation adds "AI Milestones: The Acceleration" as a title (`AIMilestones.tsx:147`). The `showTitle` prop defaults to `true`, so this title appears in standalone mode, though it could be suppressed when embedded in Part1Economics.
   - **Spec reference**: Lines 13-14 ("Continues from Section 1.4")
   - **Implementation**: `AIMilestones.tsx:132-149`

5. **Company Logos Not Implemented (Low)**: Spec mentions "Optional: Small logos next to names (if available/legal)". Not implemented. Marked optional in spec, so low severity.
   - **Spec reference**: Line 98
   - **Implementation**: None

6. **GPT-4 BEATS Comment Says "Moderate" but Spec Says "Large" (Informational)**: The comment on `constants.ts:20` says "moderate drop" for GPT-4, but the spec table says "Large" drop size, and the actual `impactScale` value of 1.5 correctly represents "Large". The comment is misleading but has no functional impact.
   - **Spec reference**: Line 29 (table)
   - **Implementation**: `constants.ts:20` (comment only)

### Notes

- The implementation is well-structured with clean separation between constants, the main chart component, and the marker component.
- The cost data curve in `COST_DATA` faithfully represents the uneven staircase descent described in the spec, with Claude 3.5 Sonnet creating the largest single drop (9 units, from 16 to 7).
- The previous audit's resolution items (GPT-4 impactScale fix, Claude 3.5 impactScale increase, subtitle removal) are all verified as correctly applied in the current code.
- The most significant gap is Issue #1 (drop easing): the spec explicitly differentiates small vs large drops with different animation durations (20 vs 40 frames) using `easeOutQuad`. The current implementation reveals the entire cost line uniformly, meaning all drops appear at the same speed. Implementing per-segment animated drops that "cause" the line to step down at different speeds would more closely match the spec's intent of making the Claude 3.5 Sonnet drop "feel like a cliff."
- The integration within Part1Economics correctly positions this component at the right narration moment (~26.6s into the section).
