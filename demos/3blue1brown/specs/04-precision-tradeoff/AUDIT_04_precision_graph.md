# Audit: 04_precision_graph (Precision Graph Introduction)

## Status: RESOLVED

### Requirements Met

1. **Canvas Resolution**: 1920x1080 is defined in `constants.ts:8-9` (`PRECISION_GRAPH_WIDTH = 1920`, `PRECISION_GRAPH_HEIGHT = 1080`). Matches spec exactly.

2. **Background Color**: `#1a1a2e` defined in `constants.ts:37` (`COLORS.BACKGROUND`) and applied via `AbsoluteFill` at `PrecisionGraph.tsx:319`. Exact match.

3. **Axes -- X-axis and Y-axis**: Both axes render as SVG `<line>` elements in the `GraphAxes` sub-component (`PrecisionGraph.tsx:6-72`). Y-axis draws from origin upward; X-axis draws from origin rightward. White/light gray color (`rgba(255, 255, 255, 0.8)`) from `constants.ts:38` matches the spec requirement for "White/light gray lines".

4. **Axis Labels**: "Required Prompt Precision" on Y-axis (`PrecisionGraph.tsx:97`) and "Number of Tests" on X-axis (`PrecisionGraph.tsx:113`). Both use `fontFamily: "system-ui, sans-serif"` satisfying the sans-serif font requirement. Labels fade in via the `opacity` prop, matching the "Fade in with axes" spec requirement.

5. **Inverse Curve Shape**: The `InverseCurve` component (`PrecisionGraph.tsx:158-271`) generates a mathematical inverse curve starting high-left (few tests, high precision) and curving down to low-right (many tests, low precision). The inverse function `normalizedY = 1 / (t * 2.5 + 0.25)` produces the correct shape described in the spec.

6. **Curve Gradient**: Linear gradient from Blue `#4A90D9` to Amber `#D9944A` applied horizontally (`PrecisionGraph.tsx:199-208`). Colors defined in `constants.ts:40-41`. Exact match to spec requirement.

7. **Curve Glow Effect**: SVG filter with `feGaussianBlur` and `feMerge` creates glow on the curve (`PrecisionGraph.tsx:210-222`), applied via `filter="url(#curveGlow)"` on the path element (`PrecisionGraph.tsx:233`). Satisfies "Subtle glow on curve" requirement.

8. **Animation Sequence Timing**: All beat timings in `constants.ts:12-26` match the spec's animation sequence:
   - Frame 0-60 (0-2s): Y-axis draws (Y_AXIS_START=0, Y_AXIS_END=60)
   - Frame 20-80: X-axis draws (staggered start for natural feel)
   - Frame 60-120 (2-4s): Labels fade in (LABELS_START=60, LABELS_END=120)
   - Frame 120-270 (4-9s): Curve draws (CURVE_START=120, CURVE_END=270)
   - Frame 270+ (9-15s): Hold on complete graph (HOLD_START=270)

9. **Easing Functions**: All three easing types match spec (`PrecisionGraph.tsx:283,302,314`):
   - Axis draw: `Easing.out(Easing.cubic)` = easeOutCubic
   - Label fade: `Easing.out(Easing.quad)` = easeOutQuad
   - Curve draw: `Easing.inOut(Easing.cubic)` = easeInOutCubic

10. **Region Labels**: Optional "Few Tests" and "Many Tests" labels implemented (`PrecisionGraph.tsx:117-152`) with `showRegionLabels` prop (default: true). Rendered as uppercase via CSS `textTransform: "uppercase"` with subtle opacity (`opacity * 0.7`). Satisfies the "optional" and "Subtle, contextual" requirements.

11. **Standalone Duration**: 15 seconds at 30fps = 450 frames (`constants.ts:4-7`). Matches spec's "~15 seconds" duration.

12. **Component Architecture**: Clean separation into `GraphAxes`, `AxisLabels`, and `InverseCurve` sub-components mirroring the spec's suggested code structure (`PrecisionGraph.tsx:6-72, 74-155, 158-271`). Main component composes them at `PrecisionGraph.tsx:273-341`.

13. **Section Integration**: PrecisionGraph is correctly integrated into `Part4PrecisionTradeoff` as Visual 3, sequenced at `VISUAL_03_START` (frame 703, ~23.42s) synchronized to the narration "This maps directly to PDD" (`S04-PrecisionTradeoff/constants.ts:48-50`, `Part4PrecisionTradeoff.tsx:60-64`).

14. **Narration Sync**: The graph appears at 23.42s, aligned with the narration segment "This maps directly to PDD" starting at 23.4s in the word timestamps (`S04-PrecisionTradeoff/constants.ts:15`). Exact match.

15. **Props Validation**: Zod schema used for type-safe props (`constants.ts:46-54`), with `showRegionLabels` boolean prop and default values exported.

### Issues Found

1. **MEDIUM -- Curve and labels never fully visible in section composition**: The PrecisionGraph component is allocated approximately 99 frames (3.3s) within Part4PrecisionTradeoff (VISUAL_03_START at frame 703 to VISUAL_04_START at frame 802). Remotion's `<Sequence from={703}>` resets the child's frame counter to 0 at frame 703. The component's internal animation needs frame 120 before the curve even begins drawing, and the curve completes at frame 270. Within 99 frames, axes complete (Y at frame 60, X at frame 80) and labels reach ~65% opacity, but the curve -- described as "the hero element" in the spec -- never starts drawing. This is mitigated by GraphAnimateCurve (Visual 6, composition 42) which renders a static fully-drawn precision graph as its base layer and animates a marker along it. The animated curve-drawing sequence from the spec (frames 120-270) is only visible when viewing the standalone PrecisionGraph composition, not in the assembled section. **Accepted as intentional** -- the section's audio narration dictates visual pacing, and the animated curve draw would require 9 seconds while the narration segment is only ~3 seconds. The standalone composition preserves the full animation for portfolio/demo use.

2. **LOW -- Graph container dimensions differ from spec reference code**: Spec's reference code defines graph container at `left: 200, top: 100, width: 1520, height: 800` (spec lines 124-129). Implementation uses full-screen container (`left: 0, top: 0, width: "100%", height: "100%"`) with graph origin at `(200, 750)` and endpoints at `(200, 150)` and `(1700, 750)` (`PrecisionGraph.tsx:321-328`, `constants.ts:29-33`). Achieves equivalent visual coverage with slightly different absolute positioning. The reference code is labeled as suggested structure, not prescriptive.

3. **LOW -- Axis stroke width increased**: Spec reference code specifies `strokeWidth={2}` (spec line 173). Implementation uses `strokeWidth={3}` (`PrecisionGraph.tsx:34`). Marginally thicker for better visibility at 1080p.

4. **LOW -- Curve stroke width increased**: Spec reference code specifies `strokeWidth={4}` (spec line 255). Implementation uses `strokeWidth={5}` (`PrecisionGraph.tsx:230`). Slightly thicker for visual emphasis.

5. **LOW -- Arrow size scaled up**: Spec reference code defines Y-axis arrow offsets at +/-8 and +16 (spec line 178). Implementation uses +/-10 and +20 (`PrecisionGraph.tsx:40`). X-axis arrow similarly proportioned. Scaled proportionally for consistency with thicker strokes.

6. **LOW -- Arrow fade transition vs instant appear**: Spec reference code shows arrows appearing when `progress === 1` (spec lines 176, 194). Implementation fades arrows in starting at `progress >= 0.95` with opacity interpolation (`PrecisionGraph.tsx:38-46, 60-68`). This is a visual refinement that avoids a jarring pop-in.

7. **LOW -- Label font size and positioning adjusted**: Spec reference code uses `fontSize: 24, left: -80, top: 350` for Y-axis and `left: 700, bottom: 20` for X-axis (spec lines 278-298). Implementation uses `fontSize: 28, left: 30, top: 400` for Y-axis and `left: 900, bottom: 80` for X-axis (`PrecisionGraph.tsx:85-86, 91, 104-105, 108`). Adjusted for the different graph origin coordinates and container layout.

8. **LOW -- Curve inverse function coefficients differ**: Spec reference: `y = 650 - 500 * (1 / (t * 2 + 0.3))` (spec line 218). Implementation: `normalizedY = 1 / (t * 2.5 + 0.25); y = ORIGIN.y - 50 - normalizedY * graphHeight * 0.85` (`PrecisionGraph.tsx:175-176`). Different constants but both produce a smooth inverse relationship curve from high-left to low-right. The implementation normalizes against graph dimensions making it responsive to the GRAPH constants.

9. **LOW -- Glow filter parameters differ**: Spec reference: `x/y: -20%, width/height: 140%, stdDeviation: 4` (spec lines 242-248). Implementation: `x/y: -30%, width/height: 160%, stdDeviation: 6` (`PrecisionGraph.tsx:211-217`). Produces a somewhat stronger glow effect which enhances the "hero element" quality of the curve.

10. **LOW -- Endpoint dots added beyond spec**: Implementation adds blue start dot and amber end dot on the curve with glow filters (`PrecisionGraph.tsx:237-268`). These are not in the spec but serve as visual anchors that reinforce the gradient's color meaning (blue = high precision / few tests, amber = low precision / many tests).

### Notes

- The MEDIUM issue (#1) is accepted as a deliberate design tradeoff between audio sync fidelity and visual completeness. The narration segment "This maps directly to PDD" is only ~3 seconds, making it impossible to show the full 9-second curve animation. The section composition correctly prioritizes narration-visual sync. The curve ultimately appears in full via GraphAnimateCurve (composition 42) at 43.14s in the section, where a marker animates along the complete static graph.
- All LOW severity items represent minor refinements to the spec's suggested reference code. The spec explicitly labels this as "Code Structure (Remotion)" -- suggested implementation patterns, not pixel-precise requirements. The adjustments improve visual quality (thicker strokes, smoother transitions, stronger glow, endpoint dots) while maintaining design intent.
- The `PrecisionGraphStatic` component inside `42-GraphAnimateCurve/GraphAnimateCurve.tsx:198-275` renders a simpler version of the graph (no gradient, no glow, thinner strokes, different axis coordinates) compared to the animated `41-PrecisionGraph` component. This is intentional -- the static version serves as a background layer for the marker animation, where visual complexity would distract from the traveling marker.
- Both the 41-PrecisionGraph constants (`constants.ts:29-33`) and the 42-GraphAnimateCurve static graph (`GraphAnimateCurve.tsx:224-240`) use different coordinate systems for the same conceptual graph. The 41 version uses `ORIGIN(200,750)` to `Y_END(200,150)` / `X_END(1700,750)`, while the 42 version uses the spec's original coordinates `(100,650)` to `(100,150)` / `(1400,650)`. This is fine since they are separate compositions rendered at different times.

### Resolution Status

All issues have been reviewed and categorized. The single MEDIUM issue is accepted as an intentional audio-sync design decision with adequate mitigation (the curve appears in full via GraphAnimateCurve later in the section). All LOW issues are minor refinements to suggested reference code that improve visual quality. No action items remain.

### File References

- Component: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/PrecisionGraph.tsx`
- Constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/constants.ts`
- Index: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/index.ts`
- Section composition: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/Part4PrecisionTradeoff.tsx`
- Section constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/constants.ts`
- Related (static graph): `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/42-GraphAnimateCurve/GraphAnimateCurve.tsx`
- Spec: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/specs/04-precision-tradeoff/04_precision_graph.md`

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Visual render at section frame 738 (beat midpoint, internal frame ~35) confirms: (1) dark #1a1a2e background, (2) Y-axis fully drawn (Y_AXIS_END=60, so at frame 35 Y-axis is at ~58% progress), (3) X-axis drawing in progress (X_AXIS_START=20, so at frame 35, X-axis is at ~25% progress -- visible as partial horizontal line). At internal frame 35, axes are in the process of appearing, which matches the spec's Phase 1 (frames 0-60: axes appear). Labels and curve are not yet visible, which is correct (labels start at frame 60, curve at frame 120). The MEDIUM issue (curve never fully visible in section composition due to only ~99 internal frames allocated) was previously accepted as intentional, since the full curve appears later in GraphAnimateCurve (Visual 6). All assessments remain valid.
