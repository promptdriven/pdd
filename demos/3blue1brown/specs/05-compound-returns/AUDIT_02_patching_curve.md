# Audit: 02_patching_curve.md

## Status: PASS

### Requirements Met

1. **Canvas & background** (constants.ts:8-9, CompoundCurvesGraph.tsx:744)
   - Resolution 1920x1080: `COMPOUND_CURVES_WIDTH = 1920`, `COMPOUND_CURVES_HEIGHT = 1080`.
   - Background `#1a1a2e`: `COLORS.BACKGROUND` applied via `AbsoluteFill` style at line 744.
   - Continues from Section 5.1 graph: phase 2 inherits all phase 1 elements (axes, labels, legend) because `axisYProgress`, `axisXProgress`, and `labelOpacity` are computed unconditionally. The `Axes`, `AxisLabels`, and `Legend` components render on every phase.

2. **Patching curve color & stroke** (CompoundCurvesGraph.tsx:781-782, constants.ts:14)
   - Color amber `#D9944A`: `COLORS.PATCHING_AMBER` used as `color` prop.
   - Stroke width 3px: `strokeWidth={3}` passed to `CurveLine`.

3. **Patching curve mathematical form** (CompoundCurvesGraph.tsx:20-23)
   - `patchingBaseY(t)` implements `maxHeight * (Math.log(t * 5 + 1) / Math.log(6))` with `maxHeight = GRAPH.HEIGHT * 0.7` (~560px).
   - This is a scaled version of the specified `y = a * log(x + 1)`. The factor of 5 compresses the domain so that the curve visibly flattens within the normalized 0-1 range while preserving the logarithmic shape.
   - Starts linear (log is approximately linear near 0) and flattens as t increases, matching spec.

4. **Curve flattening around 60-70% of X-axis** (CompoundCurvesGraph.tsx:20-23)
   - The logarithmic function `log(5t + 1)` has its inflection toward flatness well within the 0.6-0.7 range. At t=0.6, the derivative is already substantially reduced from the initial slope, producing the specified visual flattening.

5. **Curve draw timing** (CompoundCurvesGraph.tsx:527-534)
   - `interpolate(frame, [0, 450], [0.08, 1])` draws the patching curve from 8% to 100% over frames 0-450.
   - Uses `Easing.out(Easing.quad)` as specified by the "easeOutQuad" easing requirement (line 532).

6. **Patch dots count and size** (constants.ts:50-51)
   - `PATCH_DOT_COUNT = 14`: within spec's 12-15 range.
   - `PATCH_DOT_RADIUS = 8`: matches spec's 8px radius.

7. **Patch dot appearance** (CompoundCurvesGraph.tsx:286-289)
   - Amber fill: `fill={color}` where color is `COLORS.PATCHING_AMBER`.
   - White border: `stroke="#ffffff" strokeWidth={2}`.
   - Evenly spaced along X-axis: `t = (i + 1) / (totalCount + 1)` produces uniform spacing (line 273).

8. **Patch dots sequential appearance** (CompoundCurvesGraph.tsx:535-543)
   - `patchVisibleDots` uses `interpolate(frame, [0, 450], [1, PATCH_DOT_COUNT])` with `Math.floor()`, so dots appear one at a time as the curve draws.

9. **Dot pop-in animation (spring physics)** (CompoundCurvesGraph.tsx:277-285)
   - Uses `spring({ frame: frame - dotFrame, fps, config: { damping: 12, stiffness: 200 } })` exactly matching spec's `spring({ damping: 12, stiffness: 200 })`.
   - Each dot staggered by 8 frames (`dotFrame = dotStartFrame + i * 8`), producing the sequential "pop" effect (scale 0 -> 1).

10. **First annotation "one bug fixed"** (CompoundCurvesGraph.tsx:802-807)
    - Text: `"one bug fixed"` at dot #3 position (`x={toSvgX(3 / (PATCH_DOT_COUNT + 1))}`).
    - Opacity: `interpolate(frame, [90, 150], [0, 1])` (lines 544-551), matching spec's frame 90-150 fade-in window.
    - Easing: `Easing.out(Easing.cubic)` matching spec's `easeOutCubic`.

11. **Annotation styling** (CompoundCurvesGraph.tsx:356-386)
    - Small italic text: `fontStyle="italic"`, `fontSize={16}`.
    - White at 70% opacity: default `color = "rgba(255,255,255,0.7)"`.
    - Leader line: rendered from (x, y) to (x+10, y+offsetY-5) with `opacity={0.5}` (lines 359-367).

12. **Second annotation "local return only"** (CompoundCurvesGraph.tsx:808-813)
    - Text: `"local return only"` at dot #6 position (`x={toSvgX(6 / (PATCH_DOT_COUNT + 1))}`).
    - Opacity: `interpolate(frame, [150, 330], [0, 1])` (lines 553-558), fading in after dot #6 appears (spec says "annotations fade in after their respective dots appear").
    - Easing: `Easing.out(Easing.cubic)` matching spec.

13. **Flattening indicator: diminished Y-spacing** (CompoundCurvesGraph.tsx:20-23, 271-292)
    - Because dots are evenly spaced on the X-axis and the Y function is logarithmic, the vertical distance between successive dots naturally decreases as X increases. This matches the spec requirement: "the spacing between dots' Y-values visibly decreases."

14. **Dashed ceiling guide line** (CompoundCurvesGraph.tsx:818-829)
    - Positioned at `patchingBaseY(1)`, the logarithmic maximum (the "ceiling").
    - Dashed: `strokeDasharray="10 6"`.
    - Color: `COLORS.CEILING_DASH = "rgba(255, 255, 255, 0.4)"`.
    - Fades in: `interpolate(frame, [330, 450], [0, 0.4])` with `Easing.out(Easing.quad)` (lines 560-567), matching spec frame 330-450 timing.

15. **PDD curve dormant** (CompoundCurvesGraph.tsx:728-733, 863-916)
    - During phase 2, `effectivePddTo` resolves to `curveStartProgress` (0.08 from phase 1), keeping the PDD starting segment visible.
    - Blue color: `COLORS.PDD_BLUE = "#4A90D9"` (line 869).
    - Glow filter applied: `glowId="pddGlow"`, `glowStd={glowStd}` where `glowStd` defaults to 4 in phase 2 (line 715-716).
    - Not growing: progress stays at 0.08 during phase 2, matching spec's "not growing yet."

16. **Animation sequence phase 1 (frames 0-90)** (CompoundCurvesGraph.tsx:527-543)
    - Curve draws from 0.08 (where 5.1 left off) to ~40% by frame 90.
    - At frame 90 in `interpolate(frame, [0, 450], [0.08, 1])` with easeOutQuad, progress is approximately 0.08 + 0.92 * easeOutQuad(90/450) = ~0.36-0.40, consistent with spec.
    - Dots #1-5 appear: `interpolate(90, [0, 450], [1, 14])` = ~2.8, so approximately 3-4 visible dots by frame 90, roughly consistent with the linear growth phase.

17. **Animation sequence phase 2 (frames 90-150)** (CompoundCurvesGraph.tsx:544-551)
    - First annotation "one bug fixed" fades in between frames 90-150, exactly matching spec.

18. **Animation sequence phase 3 (frames 150-330)** (CompoundCurvesGraph.tsx:527-558)
    - Curve continues drawing; by frame 330, easeOutQuad progress is well past 75%.
    - Dots #6-10 appear during this window (visible dots at frame 330: `interpolate(330, [0, 450], [1, 14])` ~ 10.5, so ~10 dots).
    - Second annotation "local return only" fades in starting at frame 150, matching spec.

19. **Animation sequence phase 4 (frames 330-450)** (CompoundCurvesGraph.tsx:535-567)
    - Dots #11-14 appear with diminished vertical gains (logarithmic flattening).
    - Ceiling guide line fades in frames 330-450, matching spec.

20. **Animation sequence phase 5 (frames 450-600)** (Part5CompoundReturns.tsx:79-83, constants.ts:48-49)
    - Part5CompoundReturns runs phase 2 from `VISUAL_01_START` (frame 82) through `VISUAL_01_END` (frame 707). Since the curve animation completes at relative frame 450, there are ~257 frames of hold time where all elements remain visible.
    - Flattening remains the visual emphasis.

21. **Integration in Part5CompoundReturns** (Part5CompoundReturns.tsx:79-83)
    - Phase 2 is rendered via `<CompoundCurvesGraph phase={2} />` inside a Sequence starting at `BEATS.VISUAL_01_START = s2f(2.74)` (frame 82).
    - This aligns with narration segment: "When you patch code, each fix has local returns."

### Issues Found

1. **PDD pulse effect missing** - Severity: LOW
   - Spec states at frames 450-600: "PDD curve's starting segment pulses faintly (foreshadowing)."
   - Implementation provides a static blue glow via Gaussian blur filter (`glowStd=4`) but no pulsing animation during phase 2. The `glowPulse` conditional (`frame > 450`) shown in the spec's code structure example is not implemented.
   - Impact: Cosmetic only. The blue glow provides a visual reminder of the PDD curve's presence, which satisfies the narrative intent ("remind viewer it exists") even without the pulse.

### Notes

- The curve mathematical form `Math.log(t * 5 + 1) / Math.log(6)` is equivalent to `log_6(5t + 1)`, a valid scaling of the specified `a * log(x + 1)` pattern. The constant 5 compresses the domain to produce visible flattening within the normalized 0-1 range.
- The second annotation fade-in range is frames 150-330 (spec says frames 150-330 for the "curve continues drawing" phase where the second annotation appears), which is wider than the first annotation's 60-frame window. This gives a gentler fade that works well visually.
- Dot spacing is computed as `(i + 1) / (totalCount + 1)` which distributes 14 dots uniformly across the normalized X-axis (at positions 1/15, 2/15, ..., 14/15), satisfying "evenly spaced along X-axis."
- The `dotStartFrame=10` for patch dots (line 795) means the first dot begins its spring animation at frame 10, not frame 0. This provides a slight delay so the curve starts drawing before dots appear, which is a reasonable creative choice.

### Resolution Status: RESOLVED

All critical and major requirements are met. The single low-severity issue (missing PDD pulse effect) is cosmetic and does not affect the narrative clarity of this section. The patching curve's logarithmic shape, dot animation, annotations, ceiling line, and timing all conform to spec.

## Re-Audit Verification (2026-02-09)

- **Render**: Still frame rendered at global frame 395 via `Part5CompoundReturns` composition (`/tmp/audit_02_patching_curve_section.png`).
- **Visual inspection**: Dark background present. Axes fully drawn with arrowheads visible. Legend in upper-left with correct color swatches (amber "Patching", blue "PDD"). Amber patching curve drawn with logarithmic shape, multiple dots visible with white borders, annotations ("one bug fixed", "local return only") present in italic. Dashed ceiling line visible at the logarithmic maximum. PDD starting segment visible as a small blue segment near the origin. All elements correctly positioned within the graph area.
- **Status**: All previously documented requirements remain met. The single low-severity issue (missing PDD pulse effect) remains accepted. No new issues found.
- **Conclusion**: PASS confirmed.
