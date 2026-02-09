# Audit: Compound Curves Introduction (Section 5.1)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and Background**: Spec requires 1920x1080 with dark background `#1a1a2e`. Implementation uses `COMPOUND_CURVES_WIDTH = 1920`, `COMPOUND_CURVES_HEIGHT = 1080`, SVG viewBox `"0 0 1920 1080"`, and `COLORS.BACKGROUND = "#1a1a2e"`. Match confirmed in `constants.ts` lines 4-9 and 12-13.

2. **Axis Drawing (Y-axis)**: Spec requires Y-axis draws upward from origin over frames 0-60 with `easeOutCubic`. Implementation uses `interpolate(frame, [0, 60], [0, 1], { easing: Easing.out(Easing.cubic) })` at `CompoundCurvesGraph.tsx` lines 500-505. Exact match.

3. **Axis Drawing (X-axis)**: Spec requires X-axis draws rightward from origin over frames 15-75 with `easeOutCubic`. Implementation uses `interpolate(frame, [15, 75], [0, 1], { easing: Easing.out(Easing.cubic) })` at lines 506-511. Exact match.

4. **Axis Appearance**: Spec requires clean, minimal white/light gray lines `rgba(255, 255, 255, 0.8)`. Implementation uses `COLORS.AXIS_WHITE = "rgba(255, 255, 255, 0.8)"` from `constants.ts` line 18, applied to both axis lines at `CompoundCurvesGraph.tsx` lines 69 and 86. Exact match.

5. **Arrowheads**: Spec requires arrowheads at axis ends. Implementation renders polygon arrowheads that fade in when progress exceeds 0.95 (lines 73-78 for Y, lines 90-95 for X). Present and functional.

6. **Label/Legend Fade Timing**: Spec requires labels and legend fade in over frames 60-120 with `easeOutQuad`. Implementation uses `interpolate(frame, [60, 120], [0, 1], { easing: Easing.out(Easing.quad) })` at lines 512-517. Exact match.

7. **X-Axis Label**: Spec requires "Time" below X-axis, centered, sans-serif, 24pt, white with 90% opacity. Implementation renders "Time" at the midpoint of X range, `fontSize={24}`, `fontFamily="system-ui, sans-serif"`, with `opacity={opacity * 0.9}` at lines 105-115. Match.

8. **Y-Axis Label**: Spec requires "Cumulative Value of Investment" rotated along Y-axis, sans-serif, 24pt, white with 90% opacity. Implementation renders the correct text, rotated -90 degrees, `fontFamily="system-ui, sans-serif"`, `opacity={opacity * 0.9}` at lines 117-128. Match (see Issue #2 for font size deviation).

9. **Legend Box**: Spec requires "Patching" with amber `#D9944A` swatch and "PDD" with blue `#4A90D9` swatch in a legend box with subtle border. Implementation has a rect with border `rgba(255, 255, 255, 0.2)` at `GRAPH.LEGEND_X: 200, GRAPH.LEGEND_Y: 130`, line swatches using `COLORS.PATCHING_AMBER` (`#D9944A`) and `COLORS.PDD_BLUE` (`#4A90D9`) at lines 133-181. Colors verified in `constants.ts` lines 14-15. Match.

10. **Curve Start Progress**: Spec requires both curves begin at origin over frames 120-210 to 0.08 (first ~8%) with `easeInOutCubic`. Implementation uses `interpolate(frame, [120, 210], [0, 0.08], { easing: Easing.inOut(Easing.cubic) })` at lines 518-523. Exact match.

11. **Both Curves Start Similarly**: Spec requires both start at similar slopes. Implementation uses the same `curveStartProgress` value for both curves in Phase 1. Both start from origin (t=0). At small t values, both `patchingBaseY` and `pddY` produce similar small values, so they appear nearly overlapping. Match.

12. **Easing Functions**: All three spec-required easings are correctly implemented: `easeOutCubic` for axes, `easeOutQuad` for labels, `easeInOutCubic` for curve start. Verified at lines 504, 510, 516, 522.

### Issues Found

1. **PDD Curve Potential Double-Rendering in Phase 1** (Severity: Low)
   - The main PDD curve block at lines 863-916 renders when `effectivePddTo > 0`. For Phase 1, `effectivePddTo` resolves to `curveStartProgress` (line 733). After frame 120, this becomes > 0, so the main block renders the PDD curve.
   - A separate Phase 1-only block at lines 918-927 also renders the PDD curve when `phase === 1 && curveStartProgress > 0`.
   - This means the PDD curve is drawn twice in Phase 1 after frame 120: once at lines 863-916 (main block) and once at lines 918-927 (Phase 1 block). Both use the same color, from/to, and strokeWidth, so the visual impact is two overlapping identical paths. This causes no visible error but doubles the SVG path elements unnecessarily.
   - **Files**: `CompoundCurvesGraph.tsx` lines 728-733 and 918-927.

2. **Y-Axis Label Font Size Deviation** (Severity: Low)
   - Spec requires 24pt for both axis labels.
   - X-axis label "Time" uses `fontSize={24}` (line 109). Correct.
   - Y-axis label "Cumulative Value of Investment" uses `fontSize={22}` (line 122). Should be 24 per spec.
   - **File**: `CompoundCurvesGraph.tsx` line 122.

3. **Graph Margin Positioning Differs from Spec Code Snippet** (Severity: Low)
   - Spec code snippet uses `left: 200, top: 80, width: 1520, height: 850` for the graph container.
   - Implementation uses `GRAPH.LEFT: 140, GRAPH.RIGHT: 1780, GRAPH.TOP: 100, GRAPH.BOTTOM: 900` (effective width 1640, height 800) in `constants.ts` lines 28-47.
   - The implementation uses a full-width SVG with viewBox coordinates rather than absolute div positioning, which is an acceptable architectural choice, but the graph occupies a slightly different region than the spec code suggests. Both approaches provide generous margins.
   - **File**: `constants.ts` lines 28-47.

4. **Section Duration in Orchestration is Shorter Than Spec** (Severity: Medium)
   - Spec says duration is ~10 seconds (frames 0-300 at 30fps).
   - The `CompoundCurvesGraph` component supports the full 300-frame Phase 1 sequence internally.
   - However, in the `Part5CompoundReturns` orchestration, Phase 1 is allocated from `VISUAL_00_START` (frame 0) to `VISUAL_00_END` (frame 56, ~1.86 seconds) per `S05-CompoundReturns/constants.ts` line 45.
   - This means Phase 1 only runs for ~1.86 seconds in the actual composition. Since axes take 60 frames (2s) to draw in the component, the full axis drawing animation would not complete before the section transitions to Phase 2.
   - The narration timing drives this: "Let's talk about compound returns" is only ~2.7 seconds, and Phase 2 begins at that point. The spec's 10-second duration does not align with the narration-driven beat structure.
   - **Files**: `S05-CompoundReturns/constants.ts` lines 44-45; `CompoundCurvesGraph.tsx` lines 500-523.

### Notes

- The component is implemented as a multi-phase design (`phase` prop 1-5) within a single `CompoundCurvesGraph` component. Phase 1 corresponds to this spec's intro section. This is a clean architectural choice that allows the graph to build upon itself across sections 5.1 through 5.5.
- The `Part5CompoundReturns` orchestrator in `S05-CompoundReturns/` correctly instantiates `CompoundCurvesGraph` with `phase={1}` for the first visual beat.
- The orchestrator uses narration-synced BEATS timing derived from Whisper word timestamps, which naturally compresses Phase 1 relative to the spec's standalone 10-second estimate.
- Color constants are centralized in `constants.ts` and verified as matching spec values exactly: `#1a1a2e` (background), `#D9944A` (amber), `#4A90D9` (blue), `rgba(255, 255, 255, 0.8)` (axes).
- The implementation includes additional infrastructure (wobble dips, cost callout, gap region, etc.) for later phases that does not interfere with Phase 1 rendering due to the `phase >= N` guards throughout.
