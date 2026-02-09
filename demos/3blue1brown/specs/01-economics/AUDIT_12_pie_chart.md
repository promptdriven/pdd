# Audit: Maintenance Pie Chart (Section 1.11 / Visual 22)

## Status: PASS

All core requirements from the spec are faithfully implemented. The component is well-structured across four files (PieChart.tsx, AnimatedPieSegment.tsx, constants.ts, index.ts) with clean separation of concerns. Only low-severity font size deviations remain, which are intentional design choices for readability at video resolution.

### Requirements Met

1. **Canvas (constants.ts:7-8, PieChart.tsx:107-110)**: Resolution 1920x1080 (`PIE_CHART_WIDTH=1920`, `PIE_CHART_HEIGHT=1080`). Background `#1a1a2e` (`COLORS.BACKGROUND`). Chart centered at (960, 560) via `CHART_CENTER` (constants.ts:66-69), offset slightly below true center to accommodate the title. All match spec.

2. **Segment 1 - Initial Development (constants.ts:47-54)**: Size is 15% of pie (middle of spec's 10-20% range). Color `#4A90D9` (cool blue). Start angle 0 degrees, end angle 54 degrees (15% of 360 = 54, consistent with spec's "~55 degrees"). Label "Initial Development". Percentage label "10-20%". All match spec exactly.

3. **Segment 2 - Maintenance (constants.ts:55-63)**: Size is 85% of pie. Color `#D9944A` (warm amber). Start angle 54 degrees (where blue ends), end angle 360 degrees (enormous arc). Label "Maintenance". Percentage label "80-90%". All match spec exactly.

4. **12 o'clock start position (AnimatedPieSegment.tsx:16-18, PieChart.tsx:14-16)**: `degreesToRadians()` subtracts 90 from the degree value before converting, correctly rotating the coordinate system so 0 degrees points up (12 o'clock). Both PieChart.tsx and AnimatedPieSegment.tsx contain this function. Matches spec requirement that segments draw from 12 o'clock.

5. **Clockwise segment draw animation (AnimatedPieSegment.tsx:59-68)**: The `animatedEndAngle` interpolates from `startAngle` to `endAngle` over the frame range, producing a clockwise sweep. The blue segment sweeps a small arc (0 to 54 degrees), the amber segment sweeps an enormous arc (54 to 360 degrees). The visual disparity in arc length correctly tells the story as spec requires.

6. **Animation sequence timing (constants.ts:17-30)**: All six phases match the spec frame-for-frame:
   - Frame 0-60: Fade out period (`FADE_OUT_START=0`, `FADE_OUT_END=60`)
   - Frame 60-120: Base circle outline appears (`BASE_APPEAR_START=60`, `BASE_APPEAR_END=120`)
   - Frame 120-180: Blue segment draws clockwise (`BLUE_SEGMENT_START=120`, `BLUE_SEGMENT_END=180`)
   - Frame 180-300: Amber segment draws clockwise (`AMBER_SEGMENT_START=180`, `AMBER_SEGMENT_END=300`)
   - Frame 300-360: Percentages fade in (`PERCENTAGES_START=300`, `PERCENTAGES_END=360`)
   - Frame 360-450: Hold with pulse on maintenance segment (`PULSE_START=360`, `PULSE_END=450`)

7. **Base circle outline (PieChart.tsx:132-162)**: An SVG circle at CHART_CENTER with CHART_RADIUS, fill "none", white stroke at 15% opacity, strokeWidth 2. Appears with eased opacity from frames 60-120. Includes a soft feDropShadow filter. Matches spec's "Pie chart base appears (circle outline)" requirement.

8. **Label appearance timing (PieChart.tsx:57-78)**: "Initial Development" label fades in near the end of the blue segment draw (frames 150-180, using `BLUE_SEGMENT_END - 30` to `BLUE_SEGMENT_END`). "Maintenance" label fades in near the end of the amber segment draw (frames 240-300, using `AMBER_SEGMENT_END - 60` to `AMBER_SEGMENT_END`). Both use `Easing.out(Easing.quad)`. Matches spec requirement that labels appear as their respective segments draw in.

9. **Percentages fade in (PieChart.tsx:82-91)**: Opacity interpolated from frames 300-360 with `Easing.out(Easing.quad)`. Matches spec's frame 300-360 range and `easeOutQuad` easing.

10. **Easing functions**:
    - Segment draw: `Easing.inOut(Easing.cubic)` (AnimatedPieSegment.tsx:66) matches spec's `easeInOutCubic`.
    - Labels fade: `Easing.out(Easing.quad)` (PieChart.tsx:65, 77, 89) matches spec's `easeOutQuad`.
    - Pulse: `Math.sin()` wave (AnimatedPieSegment.tsx:80) matches spec's `sin` wave on scale. All correct.

11. **Pulse animation (AnimatedPieSegment.tsx:76-81)**: Activates at `pulseStartFrame` (360) only when `shouldPulse=true`. Scale oscillates `1 + 0.02 * Math.sin((pulseFrame / 30) * Math.PI)`, producing range 1.0 to 1.02 to 1.0 with a ~2 second period (60 frames). Applied only to the maintenance segment (`shouldPulse={true}` at PieChart.tsx:182). Matches spec exactly: "sin wave on scale (1.0 -> 1.02 -> 1.0)".

12. **3D effect (AnimatedPieSegment.tsx:118-128)**: Subtle linearGradient goes from full color at 0%, 95% opacity at 50%, to a darkened color at 100%. The `adjustBrightness()` helper (AnimatedPieSegment.tsx:145-151) darkens the color by 20 units. Matches spec's "Subtle, not cheesy" 3D effect requirement.

13. **Drop shadow (AnimatedPieSegment.tsx:109-116)**: Soft `feDropShadow` with dx=4, dy=6, stdDeviation=8, 40% black opacity. Applied via SVG filter to each segment path. Matches spec's "Soft" drop shadow requirement.

14. **Segment separation (constants.ts:72, AnimatedPieSegment.tsx:30-31)**: `SEGMENT_GAP = 3` pixels. Applied via angle adjustment in `createArcPath()` which insets the start angle and outsets the end angle by `(gap / radius) * (180 / Math.PI)`. Within spec's 2-3px range.

15. **Stroke (constants.ts:42, 73; AnimatedPieSegment.tsx:133-134)**: White `#ffffff` color (`COLORS.STROKE`), 1px width (`STROKE_WIDTH = 1`). Applied to each segment path. Matches spec exactly.

16. **Title text (PieChart.tsx:128)**: "Where Software Costs Go". White color via `COLORS.TITLE`. Sans-serif font family ("Inter, system-ui, sans-serif"). Positioned at top of canvas (top: 60px). Matches spec content and positioning.

17. **Percentage label colors (PieChart.tsx:213-214, 249-250)**: Blue percentage uses `PIE_SEGMENTS.initialDevelopment.color` (#4A90D9). Amber percentage uses `PIE_SEGMENTS.maintenance.color` (#D9944A). Both bold (fontWeight: 700). Matches spec requirement for segment-colored, bold percentages.

18. **Label font and color (PieChart.tsx:198-203, 235-240)**: White labels (`COLORS.LABEL`), sans-serif font ("Inter, system-ui, sans-serif"), fontWeight 500. Matches spec requirement for white, sans-serif labels.

19. **Duration (constants.ts:4-6)**: 30 FPS, 15 seconds, 450 frames total (`PIE_CHART_FPS=30`, `PIE_CHART_DURATION_SECONDS=15`, `PIE_CHART_DURATION_FRAMES=450`). Matches spec's "~15 seconds" duration exactly.

20. **Integration (Part1Economics.tsx:228-233)**: PieChart is correctly imported from "../12-PieChart" (line 17) and rendered as Visual 22 with `defaultPieChartProps`. The inner `<Sequence from={-120}>` pre-advances the component by 120 frames so the base circle is already visible when the visual starts, which is a reasonable integration choice.

### Issues Found

1. **Title font size -- Low**: Spec says 32pt; implementation uses 42px (PieChart.tsx:121). This is 31% larger than spec. Intentional for readability at 1920x1080 video resolution where spec pt values translate to small on-screen sizes.

2. **Label font sizes -- Low**: Spec says 18pt for all labels; blue label uses 22px (PieChart.tsx:199), amber label uses 26px (PieChart.tsx:236). Both are larger than spec. The amber label is intentionally larger than the blue label to create visual hierarchy emphasizing the maintenance segment's dominance.

3. **Percentage font sizes -- Low**: Spec says 24pt bold for all percentages; blue percentage uses 28px (PieChart.tsx:211), amber percentage uses 36px (PieChart.tsx:248). Both are bold (fontWeight 700). The amber percentage is 50% larger than the blue, reinforcing the visual impact of the maintenance figure. Spec says uniform size; implementation differentiates for emphasis.

4. **No explicit "chaos from previous section fades out" -- Low**: Spec frames 0-60 describe "Chaos from previous section fades out." The component defines `FADE_OUT_START/END` constants (constants.ts:18-19) but the PieChart component itself does not render the previous section's content or animate its fade-out. This is handled by the parent composition (Part1Economics.tsx) via visual switching and the `from={-120}` offset, which is the correct architectural approach.

### Notes

- The connector line from the small blue segment to its external label (PieChart.tsx:259-293) is an enhancement not specified in the original spec. It improves readability by visually linking the small 15% segment to its label, which would otherwise float disconnected from the tiny arc.
- All font size deviations are consistent: sizes are uniformly scaled up from spec values, and the maintenance segment's labels are intentionally differentiated (larger) to reinforce the spec's stated goal that "The amber segment's size should be visually striking." These are deliberate design choices, not oversights.
- The arc path construction (AnimatedPieSegment.tsx:21-45) correctly handles large-arc flags for segments > 180 degrees, ensuring the amber segment renders as a major arc.
- The `adjustBrightness()` helper (AnimatedPieSegment.tsx:145-151) for the 3D gradient is robust, clamping RGB values between 0-255 and producing proper hex output.
- All HIGH and MEDIUM severity requirements -- colors, segment sizes, timing, animation behavior, easing functions, pulse effect, segment gap, stroke, start position -- are implemented exactly as specified.

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**: Amber percentage color previously corrected from white to segment color `#D9944A`. SEGMENT_GAP verified at 3px (within spec's 2-3px range). All timing constants verified frame-accurate against spec.
- **Remaining**: Low-severity font size deltas are intentional design choices for better readability and visual hierarchy at 1920x1080 video resolution. No action required.
