# Audit: 17_three_components

## Status: ISSUES FOUND

### Requirements Met

1. **Resolution and background correct** -- Canvas is 1920x1080 at 30fps with background color `#1a1a2e`, matching spec lines 14-16. Verified in `constants.ts` lines 8-9 and `COLORS.BACKGROUND` at line 57.

2. **Duration matches spec** -- Standalone composition is 25 seconds (750 frames), matching spec line 4. Verified in `constants.ts` lines 5-7.

3. **Three components present with correct colors** -- PROMPT (`#4A90D9` blue), TESTS (`#D9944A` amber), GROUNDING (`#5AAA6E` green) all present and correctly colored. Verified in `constants.ts` lines 58-60 and `ThreeComponents.tsx` lines 232-234.

4. **Component labels match spec** -- Labels now read "PROMPT"/"Intent", "TESTS"/"Constraints", "GROUNDING"/"Style", matching spec lines 33-35. Verified in `ThreeComponents.tsx` lines 232-234.

5. **Integration formula implemented** -- The IntegrationFormula component (lines 177-224) displays:
   - "Prompt + Tests + Grounding" with color-coded spans (blue/amber/green) matching spec line 292-304
   - "Intent + Constraints + Style" in gray matching spec line 302
   - "= Complete Specification" in white matching spec line 309
   - Positioned at bottom: 60, centered, matching spec line 285.

6. **Formula timing matches spec** -- Formula appears at frames 600-660, matching spec line 69 ("Frame 600-750"). Verified in `constants.ts` lines 39-40.

7. **hexToRgb helper present** -- Used for semi-transparent backgrounds on component blocks, matching spec line 245. Verified in `ThreeComponents.tsx` lines 6-10.

8. **Glow effect on components** -- `boxShadow: 0 0 ${30 * glowIntensity}px ${color}` matches spec line 251. Verified in `ThreeComponents.tsx` line 49.

9. **showFormula prop available** -- Allows toggling formula display, useful for dual-purpose usage. Verified in `constants.ts` lines 68-69 and `ThreeComponents.tsx` line 409.

### Issues Found

1. **Fundamentally different visual layout: triangle vs vertical flow** (HIGH)
   - Spec lines 75-110 define a vertical flow diagram: nozzle at top, grounding in middle, test walls constraining sides, code output at bottom -- representing the injection mold metaphor
   - Implementation uses a triangular layout with PROMPT at top (960, 180), TESTS at bottom-left (560, 700), GROUNDING at bottom-right (1360, 700), connected by triangle edges (`constants.ts` lines 48-50)
   - This is a fundamentally different visual metaphor (dependency graph vs mold injection flow)

2. **Missing flow animation through system** (HIGH)
   - Spec lines 48-68 describe a sequential flow: prompt enters nozzle with blue glow, transforms through grounding with green glow, hits wall boundaries with amber glow, code emerges at output
   - Implementation has no flow animation. Components appear via staggered scale-up (lines 238-244), edges draw in (lines 247-252), and glows intensify uniformly (lines 255-260), but nothing moves through the system
   - The spec explicitly describes material/data flowing directionally through components

3. **Missing mold walls visualization** (MEDIUM)
   - Spec lines 90-97 and lines 197-204 show test walls as physical barriers (`WallsBlock` component) with solid blocks constraining the code space
   - Implementation renders TESTS as an identical `VertexNode` to the other components -- just a labeled box, not walls

4. **Missing FlowArrow components** (MEDIUM)
   - Spec lines 182, 195, 207 reference `<FlowArrow>` components connecting prompt-to-grounding, grounding-to-walls, and walls-to-output with directional flow animation
   - Implementation has `TriangleEdge` components (lines 91-138) which are static gradient lines, not directional flow arrows

5. **Missing OutputBlock component** (MEDIUM)
   - Spec lines 100-103 and 209-213 show a distinct `OutputBlock` for generated code with success indicators (checkmarks)
   - Implementation has an inline dim code block (lines 383-406) with `opacity: 0.5`, gray styling, and an explicit "NO GLOW" comment -- no success indicators present

6. **Timeline phases compressed and reordered** (MEDIUM)
   - Spec defines 6 distinct 4-second phases: system overview (0-4s), prompt enters (4-8s), through grounding (8-12s), constrained by walls (12-16s), code emerges (16-20s), formula (20-25s)
   - Implementation runs: vertices appear in 0-1.7s, edges 2-4s, glows 4-5.3s, code 6-7.3s, hold, then formula at 20-22s. The sequential component-by-component glow phases are missing entirely

7. **Easing functions differ from spec** (LOW)
   - Spec line 318 calls for `easeOutCubic` on system fade and `easeOutQuad` on component glows
   - Implementation uses `Easing.out(Easing.back(1.5))` for vertex appearance (overshoot bounce) and `Easing.out(Easing.cubic)` for edges. No `easeOutQuad` is used for glows (glow interpolation has no easing, lines 255-260)

8. **Formula unreachable in S03-MoldThreeParts context** (MEDIUM)
   - Visual 18 in `S03-MoldThreeParts/constants.ts` runs from 278.46s to 286.34s (~7.87 seconds, ~236 frames)
   - The formula starts at frame 600 internally, which would never be reached during the S03 sequence playback
   - Within S03, only frames 0-236 of the internal timeline play: vertices (0-50), edges (60-120), glows (120-160), code (180-220)
   - The formula feature effectively only works in standalone rendering or if the composition is given more time

### Notes

- The composition is used as Visual 18 in `S03-MoldThreeParts/Part3MoldThreeParts.tsx` line 176, with `defaultThreeComponentsProps` (which sets `showFormula: true`).
- The narration at that point is: "Cramped plus tests plus grounding. Intent plus constraints plus style..." (segment 38 at 278.5s), followed by "complete specification" (segment 39 at 286.3s). The narration about "complete specification" falls AFTER the ThreeComponents visual ends and CodeOutputMoldGlows begins -- meaning the formula text would ideally need to appear within the available 7.87 seconds, not at frame 600.
- The existing audit's recommendation to create a separate "37b-MoldIntegration" composition for the Section 3.17 vertical-flow mold metaphor remains valid. The current triangle layout is appropriate for Section 6.4 (Closing) but does not match the mold injection metaphor required by Section 3.17.
- Key implementation files:
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/37-ThreeComponents/ThreeComponents.tsx`
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/37-ThreeComponents/constants.ts`
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx` (sequence integration at Visual 18)
  - `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts` (timing at lines 132-134)
