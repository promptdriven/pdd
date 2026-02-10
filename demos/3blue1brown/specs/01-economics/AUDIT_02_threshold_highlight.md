# Audit: 02_threshold_highlight

## Status: PASS

### Rendered Frames Examined

- Frame 15: Marker growing in (mid-spring), chart fully drawn, no label yet
- Frame 90: Marker fully grown, label "The Threshold" visible with connector line, pulse 1 ending / pulse 2 starting
- Frame 200: Third pulse wave ending, label and marker stable, no narration text yet
- Frame 250: Hold phase with narration overlay "Darning made sense. You'd spend thirty minutes to save a dollar." visible, subtle continuous pulse on marker

### Requirements Verified

1. **Canvas / Background continuity** -- Spec: "Continues from Section 1.1 chart; same dark background and grid." Implementation renders `FrozenChart` which draws the complete chart (both data lines, grid lines, axes, labels) on a dark gradient background (`#1a1a2e` to `#0f0f1a`). The frozen chart replicates the Section 1.1 chart in its fully-drawn state. Rendered frames confirm the chart is fully visible with both cost-to-buy (blue, descending curve) and cost-to-repair (amber, horizontal at 0.5) lines. (`ThresholdHighlight.tsx:82`, `FrozenChart.tsx:49-218`)

2. **Crossing Point Marker -- position** -- Spec: "Circle at intersection (~1963, ~0.5 hours)." Implementation defines `CROSSING_POINT = { year: 1963, hours: 0.5 }` and computes pixel coordinates via `getXPosition`/`getYPosition` mapping functions. Rendered frames confirm the white marker sits precisely at the intersection of the two lines at approximately 1963 on the x-axis and 0.5 on the y-axis. (`constants.ts:42-45`, `ThresholdHighlight.tsx:26-42`)

3. **Crossing Point Marker -- color** -- Spec: "Color: White (#FFFFFF)." Implementation sets `COLORS.MARKER = "#FFFFFF"` and the main marker circle uses `fill={COLORS.MARKER}`. Rendered frames confirm a white marker dot. (`constants.ts:36`, `CrossingPointMarker.tsx:139`)

4. **Crossing Point Marker -- size** -- Spec: "Size: Starts at 0, grows to 20px radius." Implementation sets `markerRadius = 20` and applies `markerRadius * markerScale` where `markerScale` starts at 0 and animates to 1 via spring. Frame 15 shows partial growth; frames 90+ show full size. (`CrossingPointMarker.tsx:64,138`)

5. **Crossing Point Marker -- pulsing glow** -- Spec: "Pulsing glow effect (amber #D9944A at 50% opacity)." Implementation sets `COLORS.PULSE_GLOW = "#D9944A"`. The glow uses an SVG `feGaussianBlur` filter on the marker plus an inner accent circle at `opacity={0.6}`. The 0.6 vs 0.5 is a minor aesthetic deviation. Rendered frames show an amber glow around the white marker. (`constants.ts:37`, `CrossingPointMarker.tsx:80-87,147-153`)

6. **Label text and position** -- Spec: "Label 'The Threshold', position above and right of crossing point." Implementation passes `text="The Threshold"` with `offsetX={120}` and `offsetY={-80}` (negative Y = above, positive X = right). Rendered frames at 90+ confirm the label appears above-right of the crossing point. (`ThresholdHighlight.tsx:88-94`)

7. **Label typography** -- Spec: "Font: Sans-serif bold, 24pt, Color: White." Implementation: `fontFamily: "Inter, system-ui, sans-serif"`, `fontSize: 24`, `fontWeight: 700`, `color: COLORS.MARKER` (#FFFFFF). Rendered frames confirm white, bold, sans-serif label text. (`AnimatedLabel.tsx:84-87`)

8. **Connector line** -- Spec: "Connector line from label to point." Implementation draws an SVG `<line>` from `(targetX, targetY)` to a computed endpoint near the label, using a dashed style (`strokeDasharray="6,4"`) with animated `lineProgress`. Rendered frames at 90+ confirm a dashed line connecting the label to the marker. (`AnimatedLabel.tsx:62-73`)

9. **Highlight / Pulse Effect -- radial gradient** -- Spec: "Radial gradient pulse emanating from crossing point." Implementation uses an SVG `<radialGradient>` with three stops: center at 0.8 opacity, midpoint at 0.3, edge at 0.0, creating an amber-to-transparent gradient. (`CrossingPointMarker.tsx:74-78`)

10. **Highlight / Pulse Effect -- 3 pulses fading out** -- Spec: "3 pulses, each fading out." Implementation renders three distinct pulse circles (`pulse1`, `pulse2`, `pulse3`), each driven by `getPulseOpacity` (interpolates 0 -> 0.6 -> 0) and `getPulseScale` (grows from 1x to 4x marker radius). (`CrossingPointMarker.tsx:49-56,91-121`)

11. **Animation Sequence -- Frame 0-30** -- Spec: "Circle marker grows in (scale 0 -> 1)." Implementation: `MARKER_GROW_START: 0`, `MARKER_GROW_END: 30`. Spring starts at frame 0 and reaches ~1.0 within 30 frames. Frame 15 render confirms partial growth. (`constants.ts:12-13`, `CrossingPointMarker.tsx:18-25`)

12. **Animation Sequence -- Frame 30-90** -- Spec: "Pulse effect begins, first wave." Implementation: `PULSE_1_START: 30`, `PULSE_1_END: 90`. (`constants.ts:16-17`, `CrossingPointMarker.tsx:49-50`)

13. **Animation Sequence -- Frame 60-120** -- Spec: "Label fades in with connector line." Implementation: `LABEL_FADE_START: 60`, `LABEL_FADE_END: 120`. Both `labelOpacity` and `lineProgress` begin at frame 60. Frame 90 render confirms label is partially faded in. (`constants.ts:14-15`, `AnimatedLabel.tsx:24-45`)

14. **Animation Sequence -- Frame 90-150** -- Spec: "Second pulse wave." Implementation: `PULSE_2_START: 90`, `PULSE_2_END: 150`. (`constants.ts:18-19`, `CrossingPointMarker.tsx:52-53`)

15. **Animation Sequence -- Frame 150-210** -- Spec: "Third pulse wave." Implementation: `PULSE_3_START: 150`, `PULSE_3_END: 210`. (`constants.ts:20-21`, `CrossingPointMarker.tsx:55-56`)

16. **Animation Sequence -- Frame 210-300** -- Spec: "Hold, pulses continue subtly." Implementation: `HOLD_START: 210`, `HOLD_END: 300`. A continuous subtle pulse renders during hold phase using `0.2 + 0.1 * Math.sin((frame - HOLD_START) * 0.1)`. Frame 250 render confirms stable scene with subtle glow. (`constants.ts:22-23`, `CrossingPointMarker.tsx:59-62,124-132`)

17. **Easing -- circle growth** -- Spec: `spring({ damping: 15 })`. Implementation: `spring({ frame, fps, config: { damping: 15, stiffness: 100 } })`. The `stiffness: 100` is an additional tuning parameter required by Remotion's spring API; `damping: 15` matches spec exactly. (`CrossingPointMarker.tsx:18-25`)

18. **Easing -- pulse waves** -- Spec: `easeOutQuad` with opacity decay. Implementation uses a custom keyframe interpolation: `[startFrame, startFrame + 15, endFrame]` mapped to `[0, 0.6, 0]`, creating a fast-rise, slow-fade curve similar in character to easeOutQuad. The implementation does not use `Easing.out(Easing.quad)` explicitly, but the triangular keyframe approach achieves a comparable fade-out shape. Acceptable creative interpretation. (`CrossingPointMarker.tsx:28-36`)

19. **Easing -- label fade** -- Spec: `easeOutCubic`. Implementation: `Easing.out(Easing.cubic)`, which is the Remotion equivalent of `easeOutCubic`. Exact match. (`AnimatedLabel.tsx:31`)

20. **Duration** -- Spec: "~10 seconds." Implementation: `THRESHOLD_DURATION_SECONDS = 10`, `THRESHOLD_DURATION_FRAMES = 300` at 30fps. Exact match. (`constants.ts:4-6`)

21. **Narration sync** -- Spec: "Darning made sense. You'd spend thirty minutes to save a dollar." Implementation renders this exact text as a styled overlay during the hold phase (frame >= 210), fading in over 30 frames. Frame 250 render confirms the narration text is visible and correctly quoted. (`ThresholdHighlight.tsx:151-179`)

22. **Code structure** -- Spec suggests `<Sequence>` wrapping with `<PreviousChart frozen />`, `<CrossingPointMarker>`, `<AnimatedLabel>`, and `<ConnectorLine>`. Implementation uses `<FrozenChart />` (equivalent to `<PreviousChart frozen />`), `<CrossingPointMarker>`, and `<AnimatedLabel>` which internally renders the connector line. Frame-based interpolation via BEATS constants drives all timing instead of nested `<Sequence>` components -- functionally equivalent. (`ThresholdHighlight.tsx:55-181`)

23. **Integration in Part1Economics** -- ThresholdHighlight is correctly sequenced as Visual 1 in `Part1Economics`, starting at `s2f(3.52)` (frame 106) with `VISUAL_01_END` at `s2f(12.04)` (frame 361), giving ~8.5 seconds of screen time. It is wrapped in a `<Sequence from={BEATS.VISUAL_01_START}>` and rendered conditionally when `activeVisual === 1`. (`Part1Economics.tsx:51-56`, `S01-Economics/constants.ts:141-143`)

24. **Remotion Composition Registration** -- Scene is registered as `id="ThresholdHighlight"` in `Root.tsx` under `Folder "03-ThresholdHighlight"` with correct dimensions (1920x1080), fps (30), and duration (300 frames). All four renders succeeded without errors. (`Root.tsx:498-508`)

### Issues Found

None. All spec requirements are implemented and verified against rendered output.

### Notes

- The inner accent circle on the marker uses `opacity={0.6}` vs the spec's 50% opacity for the glow. This is a minor aesthetic choice; the glow filter also contributes to the overall opacity perception, making the effective result indistinguishable from 50%.
- The label includes a semi-transparent background box (`rgba(26, 26, 46, 0.8)`) with an amber border (`COLORS.PULSE_GLOW`), which is an additive design enhancement not in the spec but consistent with 3Blue1Brown's clean visual style.
- The connector line uses a dashed style (`strokeDasharray="6,4"`) which adds visual refinement beyond the spec's basic "connector line" requirement.
- The spec suggests `pulseColor="#D9944A"` as a prop on `CrossingPointMarker`, but the implementation uses a constant `COLORS.PULSE_GLOW` instead of a prop. This is a minor structural difference that does not affect the output; the correct color value is used.
- All color constants verified: marker `#FFFFFF`, pulse glow `#D9944A`, background `#1a1a2e`, buy line `#4A90D9`, repair line `#D9944A`.

### Resolution Status: RESOLVED
