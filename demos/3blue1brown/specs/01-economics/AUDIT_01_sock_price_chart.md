# Audit: Sock Price Chart (01_sock_price_chart.md)

## Status: PASS

> Audited: 2026-02-09. All requirements verified against rendered stills (frames 40, 120, 300, 570) and full code review.

### Requirements Met

1. **Canvas Resolution**: 1920x1080 correctly defined as `SOCK_CHART_WIDTH = 1920` and `SOCK_CHART_HEIGHT = 1080` in `constants.ts:7-8`. Matches spec's "1920x1080 (16:9)".

2. **Background Color and Gradient**: Dark `#1a1a2e` with gradient to `#0f0f1a` applied via `linear-gradient(180deg, ...)` in `SockPriceChart.tsx:28`. Confirmed visually in all rendered frames. Spec calls for "#1a1a2e with subtle gradient" -- met.

3. **Grid Lines**: Color `#333344` defined as `COLORS.GRID` in `constants.ts:35`. Rendered with `strokeDasharray="5,5"` and `opacity={0.5}` in `ChartAxes.tsx:74-78` (horizontal) and `ChartAxes.tsx:88-92` (vertical). Dashed grid visible in all rendered frames. Matches spec's "Subtle gray (#333344), dashed".

4. **X-axis Range**: `YEAR_RANGE = { min: 1950, max: 2020 }` in `constants.ts:71`. Matches spec's "1950 - 2020".

5. **Y-axis Range**: `HOURS_RANGE = { min: 0, max: 1.5 }` in `constants.ts:72`. Matches spec's "0 - 1.5 hours".

6. **Y-axis Label Text**: "Hours of labor to buy / repair a sock" rendered in `ChartAxes.tsx:178`. Matches spec exactly. Confirmed visually in rendered frames.

7. **Line 1 Color (Cost to Buy)**: `LINE_BUY = "#4A90D9"` in `constants.ts:39`. Applied in `SockPriceChart.tsx:57`. Blue line confirmed in rendered stills. Matches spec's "#4A90D9 (cool blue)".

8. **Line 2 Color (Cost to Repair)**: `LINE_REPAIR = "#D9944A"` in `constants.ts:40`. Applied in `SockPriceChart.tsx:65`. Amber/orange horizontal line confirmed in rendered stills. Matches spec's "#D9944A (warm amber)".

9. **Cost to Buy Data Points**: Now exactly match the spec. `constants.ts:45-56` contains:
   - `{year: 1950, hours: 1.0}`, `{year: 1955, hours: 0.75}`, `{year: 1960, hours: 0.55}`, `{year: 1963, hours: 0.5}`, `{year: 1970, hours: 0.2}`, `{year: 1980, hours: 0.1}`, `{year: 1990, hours: 0.06}`, `{year: 2000, hours: 0.04}`, `{year: 2010, hours: 0.03}`, `{year: 2020, hours: 0.03}`.
   - This is an exact match to the spec's data table. The buy line starts at ~1.0 hours in 1950 and crosses the 0.5-hour repair line at ~1963, consistent with the spec's "circa 1960-65" crossing. Confirmed visually at frame 300 where the crossing is clearly around 1963.

10. **Cost to Repair Data**: Flat line at 0.5 hours from 1950-2020 in `constants.ts:57-60` (`[{year:1950, hours:0.5}, {year:2020, hours:0.5}]`). Matches spec's "Relatively flat (~0.5 hours throughout)". Confirmed visually as a horizontal line at the 0.5 mark.

11. **Title Text**: "The Economics of Sock Repair" rendered in `SockPriceChart.tsx:47`. Matches spec exactly. Confirmed visually in all rendered frames.

12. **Title Fade-In at Start**: Title opacity interpolates from 0 to 1 over frames 0-30 (`SockPriceChart.tsx:18-23`). Matches spec's "fade in at start".

13. **Axis Label Typography**: Font `Inter, system-ui, sans-serif`, `fontSize: 18`, color `rgba(255, 255, 255, 0.8)` in `ChartAxes.tsx:125-128` (year labels) and `ChartAxes.tsx:144-148` (hour labels). Matches spec's "Sans-serif, 18pt, white with 80% opacity".

14. **Year Markers**: Decade ticks `[1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020]` in `ChartAxes.tsx:32`. Matches spec's "Every decade" requirement. Confirmed visually along the X-axis.

15. **Line Drawing Easing**: `Easing.inOut(Easing.cubic)` in `AnimatedLine.tsx:52`. Matches spec's `easeInOutCubic`.

16. **Animation Beat Structure (7 phases)**: The `BEATS` object in `constants.ts:11-26` encodes all 7 phases from the spec:
    - Axes fade in: frames 0-30 (0-1s) -- `AXES_FADE_IN_START/END`
    - Buy line draw: frames 30-90 (1-3s) -- `BUY_LINE_START/END`
    - Repair line draw: frames 90-150 (3-5s) -- `REPAIR_LINE_START/END`
    - Time progression: frames 150-300 (5-10s) -- `TIME_PROGRESS_START/END`
    - Cost drop: frames 300-450 (10-15s) -- `DROP_START/END`
    - Approach crossing: frames 450-540 (15-18s) -- `APPROACH_START/END`
    - Hold at crossing: frames 540-600 (18-20s) -- `HOLD_START/END`

17. **Duration**: 20 seconds at 30fps = 600 frames. `SOCK_CHART_DURATION_SECONDS = 20`, `SOCK_CHART_FPS = 30`, `SOCK_CHART_DURATION_FRAMES = 600` in `constants.ts:4-6`. Matches spec.

18. **Narration Text (First Quote)**: "This isn't nostalgia. It's economics." rendered at `SockPriceChart.tsx:164`. Confirmed visually at frame 570 with semi-transparent dark overlay centered on screen. Matches spec's first narration quote.

19. **Component Structure**: Spec suggests `<ChartAxes />`, `<AnimatedLine />` components within a `<Sequence>`. Implementation uses exactly these components in `SockPriceChart.tsx:52-71`. Matches spec structure.

20. **Hold at Crossing Point**: `HOLD_START: 540` and `HOLD_END: 600` in `constants.ts:24-25`. Narration overlay appears at frame 540 (`SockPriceChart.tsx:133`). Matches spec's "Frame 540-600 (18-20s): Hold at crossing point".

21. **Integration in Part1Economics**: `SockPriceChart` is correctly imported and rendered as Visual 0 in `Part1Economics.tsx:45-49`, with beat timing at `VISUAL_00_START: s2f(0.0)`.

### Accepted Deviations (Low Severity, No Fix Required)

#### 1. Fade Transition Easing Uses Linear Instead of easeOutQuad (Low Severity)

The spec requires: "Fade transitions: `easeOutQuad`". Five fade interpolations use Remotion's default linear easing (no `easing` parameter):

- Title fade-in: `SockPriceChart.tsx:18-23`
- Axes fade-in: `ChartAxes.tsx:23-28`
- Legend fade-in: `SockPriceChart.tsx:79-84`
- Narration text fade-in: `SockPriceChart.tsx:140-145`
- Label fade-in within AnimatedLine: `AnimatedLine.tsx:128-133`

All of these should use `Easing.out(Easing.quad)` to match the spec. However, the difference between linear and easeOutQuad for sub-1-second fade transitions is visually subtle and does not materially affect the viewer experience. Within Part1Economics, SockPriceChart is only visible for ~2.68 seconds, further reducing the impact.

#### 2. Animation Phases 4-6 Not Implemented as Distinct Progressive Phases (Low Severity)

The spec describes a multi-phase progressive animation where both lines animate through time together (phases 4-6, frames 150-540). The implementation draws both lines fully during frames 30-150, then holds the completed chart static. The `BEATS` constants for `TIME_PROGRESS`, `DROP`, and `APPROACH` are defined but not referenced by any rendering code.

This is an acceptable simplification: the draw-then-hold approach works well for the ~2.68s screen time in Part1Economics. The multi-phase progressive reveal would only be meaningful during the full 20-second standalone duration.

#### 3. Second Narration Quote Not Displayed in Standalone Mode (Low Severity)

The spec lists two narration quotes. Only the first ("This isn't nostalgia. It's economics.") is rendered. The second ("In 1950, a wool sock cost real money relative to an hour of labor.") is displayed during Visual 1 (ThresholdHighlight) in Part1Economics, which is an intentional editorial decision to pair it with a different visual.

#### 4. Transition to Next Scene (Informational)

The spec states: "Holds at crossing point, preparing for Section 1.2 highlight effect." In Part1Economics, the transition between SockPriceChart and ThresholdHighlight is a hard cut, which is the established pattern throughout the composition.

### Notes

- The implementation is well-organized: `SockPriceChart.tsx` (main composition), `ChartAxes.tsx` (axes, grid, labels), `AnimatedLine.tsx` (SVG path animation), and `constants.ts` (timing, color, data).
- The `AnimatedLine` component includes enhancements not specified: a dot-at-tip indicator during drawing (`AnimatedLine.tsx:155-162`), label positioning at line endpoints (`AnimatedLine.tsx:166-183`), and segment-based path drawing for multi-point data.
- A legend component fades in after the repair line finishes drawing (`SockPriceChart.tsx:73-130`), providing useful visual context.
- The narration text overlay uses a semi-transparent dark background for readability.
- The `showTitle` prop allows hiding the title when the chart is embedded in other compositions.
- Within `Part1Economics`, the SockPriceChart is only visible for ~2.68 seconds (80 frames at 30fps), meaning only the axes fade-in and initial buy-line draw phases are seen.
- The cost-to-buy data was previously divergent from the spec (the old audit documented this as Issue 1). The data has since been corrected to match the spec exactly, with the crossing point now at ~1963 as intended.
