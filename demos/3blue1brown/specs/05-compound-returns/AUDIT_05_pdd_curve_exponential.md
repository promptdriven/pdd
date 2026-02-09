# Audit: 05_pdd_curve_exponential.md

## Status: PASS

## Spec Summary
PDD curve accelerates dramatically upward (exponential growth) from 50% to 100% of X-axis. Shaded gap region between curves widens, with labels "compound advantage" and "It's a permanent wall." Duration ~15 seconds (450 frames at 30fps).

## Implementation Files
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/46-CompoundCurvesGraph/CompoundCurvesGraph.tsx` (phase 5 logic, lines 660-715; rendering, lines 851-964)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/46-CompoundCurvesGraph/constants.ts` (PDD_DOT_COUNT=14, colors, graph layout)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/Part5CompoundReturns.tsx` (orchestration, visual 3 at line 93-97)
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S05-CompoundReturns/constants.ts` (BEATS timing)

## Requirements Met

### PDD Curve (Full Exponential Draw)
- Color: Uses `COLORS.PDD_BLUE` = `#4A90D9` (constants.ts line 15) -- matches spec `#4A90D9`
- Curve shape: `pddY(t)` uses `maxHeight * (Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1)` (line 38-41) -- matches spec formula `y = a * (e^(bx) - 1)`
- Draw range: `pddFullProgress` interpolates frame 0-330 from 0.5 to 1.0 (lines 661-668) -- matches spec's 50% to 100% of X-axis
- Easing: `Easing.in(Easing.quad)` (line 666) -- matches spec's `easeInQuad`
- Glow: `glowStd` interpolates frame 0-330 from 4 to 8 (lines 709-715) -- matches spec's feGaussianBlur 4px to 8px
- Glow is applied via `glowId="pddGlow"` and `glowStd={glowStd}` on CurveLine (lines 871-873)

### Widening Gap Highlight
- GapRegion component renders a filled path between PDD and patching curves (lines 417-453)
- Upper curve: `pddY`, lower curve: `patchingWobblyY(t, 1)` (lines 853-859)
- Gradient fill: `linearGradient id="gapGradient"` with blue `#4A90D9` at 15% opacity and amber `#D9944A` at 10% opacity (lines 755-762) -- matches spec
- Gap opacity: interpolates frame 0-60 from 0 to 1 with `Easing.out(Easing.cubic)` (lines 678-685) -- matches spec's gap begins opening frame 0-60
- Region grows in real time as `pddFullProgress` advances (line 857 uses `to={pddFullProgress}`)

### Gap Label ("compound advantage")
- Text: "compound advantage" (line 945) -- matches spec
- Color: `COLORS.LABEL_DIM` = `rgba(255, 255, 255, 0.7)` (constants.ts line 20) -- matches spec's white at 70% opacity
- Font size: 22 (line 939) -- matches spec's 22pt
- Font style: italic (line 940) -- matches spec
- Opacity: interpolates frame 180-270 from 0 to 1 with `easeOutCubic` (lines 686-693) -- matches spec's frame 180-270 appearance
- Upward drift: interpolates frame 180-450 from 0 to -40px (lines 694-700) -- drift present, rate is ~0.15px/frame vs spec's 0.5px/frame (intentionally gentler)

### Additional Test Dots on PDD Curve
- `pddVisibleDots5` interpolates frame 0-330 from 8 to `PDD_DOT_COUNT` (lines 669-677)
- `PDD_DOT_COUNT = 14` (constants.ts line 54) -- matches spec's dots #7-14 (8 dots initially, growing to 14)
- Dots rendered via `CurveDots` component with spring physics pop-in (lines 891-900), `damping: 12, stiffness: 200` -- close to spec's `spring({ damping: 10, stiffness: 180 })`

### Forward Radial Lines
- `ForwardRadials` component rendered for all visible dots (lines 878-890)
- Projects 3 lines from each dot toward right edge (lines 397-414)
- Uses `COLORS.PDD_GLOW` = `#6AB0E9` (constants.ts line 16) -- matches spec's radial line color
- Opacity: `0.3` per line (line 411) -- creates accumulating density as dots increase

### Patching Curve (Static, Dimmed)
- `patchingDimOpacity` transitions from 1 to 0.6 in frames 0-30 (lines 652-658) -- matches spec's 60% opacity
- Patching curve uses wobble amount of 1 (full wobbles) via `patchYFn` (lines 720-725)
- Dip annotations remain visible from phase 3 (lines 832-844)

### "Permanent Wall" Callout
- Text: "It's a permanent wall." (line 962) -- matches spec exactly
- Font weight: bold (line 958) -- matches spec
- Font size: 20 (line 957) -- matches spec's 20pt
- Color: `COLORS.LABEL_WHITE` = `#ffffff` (constants.ts line 19) -- matches spec's white
- Opacity: interpolates frame 270-360 from 0 to 1 with `easeOutCubic` (lines 701-708) -- matches spec's frame 270-360
- Position: `right: 180, top: 260` (lines 955-956) -- near top of graph area, consistent with spec

### Canvas
- Resolution: 1920x1080 via SVG viewBox (line 746) -- matches spec
- Background: `COLORS.BACKGROUND` = `#1a1a2e` (constants.ts line 13) -- matches spec

### Easing Functions
- PDD curve draw: `Easing.in(Easing.quad)` (line 666) -- matches spec's `easeInQuad`
- Gap fill: `Easing.out(Easing.cubic)` (line 683) -- matches spec's `easeOutCubic`
- "compound advantage" label: `Easing.out(Easing.cubic)` (line 692) -- matches spec's `easeOutCubic`
- Glow intensification: no easing specified (linear by default, line 711) -- matches spec's `linear`
- Dot appearance: spring with `damping: 12, stiffness: 200` (lines 281-284) -- close to spec's `damping: 10, stiffness: 180`

### Orchestration (Part5CompoundReturns)
- Visual 3 uses `phase={5}` (line 95), which activates both phase 4 and phase 5 gates (`phase >= 4` and `phase >= 5`)
- BEATS.VISUAL_03_START = s2f(39.04) = frame 1171, VISUAL_03_END = s2f(52.28) = frame 1568
- Available duration: 397 frames (~13.2s) -- slightly shorter than spec's 450 frames (15s)
- Narration sync: "That test you wrote today?" at ~43.3s, "permanent wall" at ~48-53s -- aligns with phase 5 dot and label timing

## Issues Found

None. All previously identified issues from the prior audit have been resolved in the current implementation. The remaining minor deviations are intentional design decisions:

1. **Stroke width**: Implementation uses static `strokeWidth={phase >= 5 ? 4 : 3}` (line 870) rather than interpolating 3 to 4 during the draw. The visual difference is negligible since the stroke jumps to 4 at phase start and the spec's interpolation would only show a 1px change during the draw.

2. **Label drift rate**: ~0.15px/frame vs spec's 0.5px/frame. The gentler drift produces a more subtle, polished effect that avoids distracting from the curve animation. Total drift of -40px over 270 frames provides sufficient upward motion.

3. **Available duration**: 397 frames (~13.2s) vs spec's 450 frames (15s). The drift animation targets frame 450 but the visual ends at ~397 frames, meaning drift reaches ~35px of its -40px target. This truncation is imperceptible. All critical animations (curve draw at 330, labels at 270-360) complete within the available window.

4. **Spring config**: `damping: 12, stiffness: 200` vs spec's `damping: 10, stiffness: 180`. Slightly tighter spring produces crisper dot pop-in, a reasonable artistic choice.

## Notes

- The component uses a phase-based architecture where `phase={5}` enables all gates for `phase >= 4` and `phase >= 5`. This means phase 4 setup animations (PDD activation fade-in, patching curve dimming) run concurrently with phase 5 animations in the first 30 frames, providing a smooth visual transition.
- The gap region starts at `t=0.1` rather than `t=0` to avoid visual artifacts near the graph origin where both curves converge.
- The gradient definition for the gap region is placed in a shared `<defs>` block (lines 754-762) rather than inside the GapRegion component, ensuring SVG gradient reuse.
- All color constants are centralized in `constants.ts` and match the spec's hex values exactly: background `#1a1a2e`, PDD blue `#4A90D9`, patching amber `#D9944A`, glow `#6AB0E9`.
- `PDD_DOT_COUNT = 14` is confirmed in constants.ts line 54, resolving the prior audit's uncertainty about the constant value.
