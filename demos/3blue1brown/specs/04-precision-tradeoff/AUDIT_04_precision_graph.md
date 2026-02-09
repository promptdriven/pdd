# Audit: 04_precision_graph (Precision Graph Introduction)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and Background**: Resolution 1920x1080 and background color #1a1a2e both match spec exactly (constants.ts lines 8-9, 37).

2. **Axis Labels**: Both "Required Prompt Precision" (Y-axis) and "Number of Tests" (X-axis) are present with the correct text (PrecisionGraph.tsx lines 97, 113). Sans-serif font family is used as specified.

3. **Axis Color**: Axes use rgba(255, 255, 255, 0.8) matching the spec's white/light gray requirement (constants.ts line 38).

4. **Curve Gradient**: Blue (#4A90D9) to Amber (#D9944A) gradient matches spec exactly (constants.ts lines 40-41). The linearGradient is applied horizontally as specified (PrecisionGraph.tsx lines 199-208).

5. **Inverse Curve Shape**: Curve starts high-left (few tests, high precision) and curves down to low-right (many tests, low precision), matching the spec's visual description. The mathematical function maintains the inverse relationship.

6. **Animation Beat Timing**: All frame-based timings match the spec precisely (constants.ts lines 12-26):
   - Y-axis: frames 0-60 (0-2s)
   - X-axis: frames 20-80 (staggered start)
   - Labels: frames 60-120 (2-4s)
   - Curve: frames 120-270 (4-9s)
   - Hold: frames 270+ (9-15s)

7. **Easing Functions**: All three easing types match spec (PrecisionGraph.tsx lines 283, 302, 314):
   - Axes: easeOutCubic
   - Labels: easeOutQuad
   - Curve: easeInOutCubic

8. **Region Labels**: Optional "Few Tests" / "Many Tests" labels implemented with `showRegionLabels` prop (default: true). Rendered uppercase via CSS textTransform (PrecisionGraph.tsx lines 117-152).

9. **Standalone Duration**: Component constants define 15 seconds at 30fps = 450 frames, matching spec's ~15 second duration (constants.ts lines 4-7).

10. **Color Palette**: All colors match spec -- background #1a1a2e, axes rgba(255,255,255,0.8), labels rgba(255,255,255,0.9), curve gradient #4A90D9 to #D9944A.

11. **Section Integration**: PrecisionGraph is correctly integrated into Part4PrecisionTradeoff as Visual 3, synced to the narration "This maps directly to PDD" at 23.42s (S04 constants.ts lines 48-50).

12. **Component Structure**: Clean separation into GraphAxes, AxisLabels, and InverseCurve sub-components matching the spec's suggested code structure. Zod schema used for props validation.

### Issues Found

1. **MEDIUM -- Curve and labels never visible in section composition**: The PrecisionGraph component is allocated only ~70 frames (2.34s) within Part4PrecisionTradeoff (VISUAL_03_START at frame 703 to VISUAL_04_START at frame 802). Remotion's `<Sequence from={703}>` resets the child's frame counter to 0 at frame 703. The internal animation requires frame 120 for labels to finish fading in and frames 120-270 for the curve to draw. Within the allocated ~70 frames, only the axes partially draw (Y-axis completes at frame 60, X-axis at frame 80) while labels barely begin fading in and the curve never starts at all. The gradient curve -- described as "the hero element" in the spec -- is never visible during this composition's appearance. Note: GraphAnimateCurve (Visual 6, composition 42) later renders a static fully-drawn version of the graph, so the curve does appear eventually, but PrecisionGraph itself never shows its animated curve draw within the section context.

2. **LOW -- Graph container dimensions differ from spec**: Spec defines graph container at left: 200, top: 100, width: 1520, height: 800 (spec lines 124-129). Implementation uses full-screen container (left: 0, top: 0, width: 100%, height: 100%) with graph origin at (200, 750) and endpoints at (200, 150) and (1700, 750) (PrecisionGraph.tsx lines 321-328, constants.ts lines 29-33). Achieves similar visual result with different absolute positioning.

3. **LOW -- Axis stroke width**: Spec specifies strokeWidth={2} (spec line 173). Implementation uses strokeWidth={3} (PrecisionGraph.tsx line 34).

4. **LOW -- Curve stroke width**: Spec specifies strokeWidth={4} (spec line 255). Implementation uses strokeWidth={5} (PrecisionGraph.tsx line 230).

5. **LOW -- Arrow size scaled up**: Spec defines Y-axis arrow offsets at +/-8 and +16 (spec line 178). Implementation uses +/-10 and +20 (PrecisionGraph.tsx line 40). X-axis arrow similarly scaled.

6. **LOW -- Arrow fade transition vs instant appear**: Spec shows arrows appearing when progress === 1 (spec lines 176, 194). Implementation fades arrows in starting at progress >= 0.95 with opacity interpolation (PrecisionGraph.tsx lines 38-46, 60-68).

7. **LOW -- Label font size and positioning**: Spec uses fontSize: 24, left: -80, top: 350 for Y-axis label and left: 700, bottom: 20 for X-axis label (spec lines 278-298). Implementation uses fontSize: 28, left: 30, top: 400 for Y-axis and left: 900, bottom: 80 for X-axis (PrecisionGraph.tsx lines 85-86, 91, 104-105, 108).

8. **LOW -- Curve inverse function formula differs**: Spec formula: `y = 650 - 500 * (1 / (t * 2 + 0.3))` (spec line 218). Implementation formula: `normalizedY = 1 / (t * 2.5 + 0.25); y = ORIGIN.y - 50 - normalizedY * graphHeight * 0.85` (PrecisionGraph.tsx lines 175-176). Different coefficients but maintains the inverse relationship shape.

9. **LOW -- Glow filter parameters differ**: Spec defines glow filter at x/y: -20%, width/height: 140%, stdDeviation: 4 (spec lines 242-248). Implementation uses x/y: -30%, width/height: 160%, stdDeviation: 6 (PrecisionGraph.tsx lines 211-217). Produces a stronger glow effect.

10. **LOW -- Endpoint dots not in spec**: Implementation adds blue start dot and amber end dot on the curve (PrecisionGraph.tsx lines 237-268). These are not specified but serve as visual enhancements.

### Notes

- The MEDIUM severity issue (#1) regarding the curve never being visible in the section context is somewhat mitigated by the fact that GraphAnimateCurve (42-GraphAnimateCurve) renders a static fully-drawn precision graph as its base layer (GraphAnimateCurve.tsx lines 198-275). This means the audience does eventually see the complete graph with the curve, but the animated curve-drawing sequence specified in the spec (the smooth left-to-right draw from frames 120-270) is never shown within the section composition. The spec describes the curve draw as the centerpiece animation ("Gradient curve is the hero element"), so this omission is notable.
- To fix the MEDIUM issue, either: (a) compress the PrecisionGraph internal timing to fit within ~70 frames, (b) extend the VISUAL_03 allocation in the section to accommodate the full 450-frame animation, or (c) accept that the standalone composition shows the full animation while the section uses the abbreviated version transitioning into GraphAnimateCurve.
- All LOW severity items are minor refinements that improve visual quality (thicker strokes, larger arrows, smoother transitions, stronger glow) without changing the fundamental design intent.
- The existing audit correctly identified most LOW deltas. This updated audit adds the MEDIUM timing issue discovered by cross-referencing the section composition's frame allocation against the component's internal animation timeline.

### File References

- Component: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/PrecisionGraph.tsx`
- Constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/constants.ts`
- Index: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/41-PrecisionGraph/index.ts`
- Section composition: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/Part4PrecisionTradeoff.tsx`
- Section constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/constants.ts`
- Related (static graph): `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/42-GraphAnimateCurve/GraphAnimateCurve.tsx`
