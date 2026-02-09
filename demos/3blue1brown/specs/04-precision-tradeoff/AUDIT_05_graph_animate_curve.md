# Audit: 05_graph_animate_curve

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and Resolution**: 1920x1080 with dark background `#1a1a2e`. Constants file defines `GRAPH_ANIMATE_WIDTH = 1920`, `GRAPH_ANIMATE_HEIGHT = 1080`, and `COLORS.BACKGROUND = "#1a1a2e"`. Matches spec exactly.

2. **Duration**: 15 seconds at 30fps (450 frames). `GRAPH_ANIMATE_DURATION_SECONDS = 15` and `GRAPH_ANIMATE_FPS = 30` in constants. Matches spec.

3. **Moving Marker with Trail**: `CurveMarker` component renders a white glowing dot (`r={12}`, `fill="white"`, SVG `feGaussianBlur` glow filter with `stdDeviation="6"`) that travels from left to right. Trail is implemented with 10 trailing circles at decreasing opacity (`1 - i * 0.1`) multiplied by 0.3, each with `r={4}`. Matches spec CurveMarker component.

4. **Marker Position Calculation**: `markerX = 100 + curveProgress * 1300` and `markerY = 650 - 500 * (1 / (curveProgress * 2 + 0.3))` at lines 303-304. Matches spec exactly. Trail points use the same formula at lines 16-17. Previously fixed per prior audit.

5. **Curve Progress Interpolation**: `interpolate(frame, [60, 300], [0, 1])` with `extrapolateLeft: "clamp"`, `extrapolateRight: "clamp"`, `easing: Easing.inOut(Easing.cubic)`. Matches spec's easeInOutCubic easing.

6. **Prompt Size Indicator**: `PromptIcon` component with 200x250 blue rectangle (`#4A90D9`), `borderRadius: 8`, 8 styled prompt lines, "parser.prompt" file header text at `fontSize: 14`, `boxShadow: '0 0 30px rgba(74, 144, 217, 0.5)'`. Matches spec's PromptIcon design.

7. **Prompt Scale**: `interpolate(curveProgress, [0, 1], [1, 0.3])` -- linear tied to marker. Matches spec (scale 1 to 0.3).

8. **Test Wall Count**: `Math.floor(interpolate(curveProgress, [0, 1], [2, 25]))` -- step function tied to marker. Walls laid out in 5-column grid with 35px horizontal and 45px vertical spacing. Each wall is 25x35 amber (`#D9944A`) with `borderRadius: 4` and `boxShadow: '0 0 15px rgba(217, 148, 74, 0.5)'`. Matches spec's TestWalls component.

9. **Position Labels**: "FEW TESTS" (active when `curveProgress < 0.3`) and "MANY TESTS" (active when `curveProgress > 0.7`). Opacity toggles between 1 and 0.3. Matches spec logic.

10. **Animation Sequence Timing**: All four phases match spec:
    - Setup: frames 0-60 (0-2s) -- `BEATS.SETUP_START=0`, `SETUP_END=60`
    - Marker travels: frames 60-300 (2-10s) -- `BEATS.TRAVEL_START=60`, `TRAVEL_END=300`
    - Arrive at right: frames 300-390 (10-13s) -- `BEATS.ARRIVE_START=300`, `ARRIVE_END=390`
    - Emphasis: frames 390-450 (13-15s) -- `BEATS.EMPHASIS_START=390`, `EMPHASIS_END=450`

11. **Final Pulse Effect**: `frame > BEATS.ARRIVE_START ? 1 + Math.sin((frame - BEATS.ARRIVE_START) * 0.1) * 0.05 : 1`. `BEATS.ARRIVE_START` equals 300, matching the spec's `frame > 300` threshold. Same sine-based pulse math.

12. **Static Graph (from Section 4.4)**: `PrecisionGraphStatic` renders axes and inverse curve path. Y-axis from (100,150) to (100,650), X-axis from (100,650) to (1400,650). Curve uses same formula as marker: `x = 100 + progress * 1300`, `y = 650 - 500 * (1 / (progress * 2 + 0.3))`. Axis labels "Required Prompt Precision" (Y) and "Number of Tests" (X) present.

13. **Color Palette**: Background `#1a1a2e`, prompt blue `#4A90D9`, walls amber `#D9944A`, marker white, labels white. All match spec.

14. **SVG Glow Filter**: `markerGlow` filter with `feGaussianBlur stdDeviation="6"` and `feMerge` compositing. Matches spec's filter definition.

15. **Section Integration**: `GraphAnimateCurve` is integrated into `Part4PrecisionTradeoff` as Visual 6, sequenced at `s2f(43.14)` (frame 1294), rendered with `defaultGraphAnimateCurveProps`. Properly connected to parent section.

### Issues Found

1. **Prompt Icon X Position Differs** (Low)
   - Spec: `position={{ x: 250, y: 400 }}`
   - Implementation: `position={{ x: 300, y: 400 }}` (line 330 of GraphAnimateCurve.tsx)
   - 50px horizontal shift from spec

2. **Test Walls X Position Differs** (Low)
   - Spec: `position={{ x: 1200, y: 400 }}`
   - Implementation: `position={{ x: 1550, y: 400 }}` (line 336 of GraphAnimateCurve.tsx)
   - 350px horizontal shift from spec. This is a more significant positional deviation, placing the walls much further right.

3. **Position Label Prop Name Differs** (Low)
   - Spec: Uses `position` prop with string values `"left"` and `"right"`
   - Implementation: Uses `positionSide` prop instead (line 171 of GraphAnimateCurve.tsx)
   - Functionally identical behavior; prop rename only

4. **Fixed Line Widths Instead of Random** (Low)
   - Spec: `width: \`${60 + Math.random() * 30}%\`` for prompt lines
   - Implementation: Fixed array `const lineWidths = [85, 70, 90, 65, 80, 75, 85, 60]` (line 71)
   - This is an intentional improvement to prevent re-render flickering in Remotion. Values fall within the spec's 60-90% range.

5. **Title Element Added** (Low)
   - Implementation adds "The Precision Tradeoff" title text centered at `top: 40` (lines 357-376)
   - Spec does not mention any title element
   - Enhancement not in spec

6. **showLabels Prop Added** (Low)
   - Implementation wraps position labels in conditional `{showLabels && ...}` (lines 341-354)
   - Spec shows labels unconditionally
   - Flexibility enhancement; defaults to `true` so default behavior matches spec

7. **Setup Opacity Fade-in Added** (Low)
   - Implementation wraps all content in a div with opacity fade from 0 to 1 over frames 0-60 (lines 283-288)
   - Spec says marker "appears" at frame 0-60 but does not specify an opacity transition for the entire scene
   - Smooth entrance enhancement

8. **Transform translate(-50%, -50%) Added** (Low)
   - Spec: `transformOrigin: 'center'` only on PromptIcon and TestWalls
   - Implementation: `transform: translate(-50%, -50%) scale(${scale})` with `transformOrigin: "center"` (lines 79, 145)
   - Adds CSS centering offset for proper center-point scaling

### Notes

- The marker position calculation was corrected in a previous audit pass and now matches the spec exactly.
- The implementation uses named BEATS constants from a constants file rather than magic numbers, which is a good engineering practice. All constant values map correctly to the spec's frame numbers.
- The COLORS constants centralize the color palette and all values match the spec's defined colors.
- The `useMemo` optimization on trail points and wall arrays is a Remotion best practice not specified but appropriate.
- The `pointerEvents: "none"` on the CurveMarker SVG is a sensible addition for compositing.
- The `fontFamily: "monospace"` on the prompt header and `fontFamily: "sans-serif"` on labels are implementation details not specified but reasonable defaults.
- The X-axis label is positioned at `y={820}` which appears to be below the 1080 viewport, potentially off-screen. This may be intentional if the graph is positioned higher, but is worth verifying visually.
- All low-severity issues are either intentional improvements (fixed line widths, useMemo, showLabels flexibility) or minor positional tweaks likely made during visual layout tuning. The 350px shift on test walls position (issue #2) is the most notable deviation and may warrant visual review to ensure the prompt icon and test walls appear balanced as the spec requires.
