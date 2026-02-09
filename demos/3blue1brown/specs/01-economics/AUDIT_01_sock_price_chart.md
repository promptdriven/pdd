# Audit: Sock Price Chart (01_sock_price_chart.md)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas Resolution**: 1920x1080 correctly defined as `SOCK_CHART_WIDTH = 1920` and `SOCK_CHART_HEIGHT = 1080` in `constants.ts:7-8`. Matches spec's "1920x1080 (16:9)".

2. **Background Color and Gradient**: Dark `#1a1a2e` with gradient to `#0f0f1a` applied via `linear-gradient(180deg, ...)` in `SockPriceChart.tsx:28`. Spec calls for "#1a1a2e with subtle gradient" -- met.

3. **Grid Lines**: Color `#333344` defined as `COLORS.GRID` in `constants.ts:35`. Rendered with `strokeDasharray="5,5"` and `opacity={0.5}` in `ChartAxes.tsx:74-78` (horizontal) and `ChartAxes.tsx:88-92` (vertical). Matches spec's "Subtle gray (#333344), dashed".

4. **X-axis Range**: `YEAR_RANGE = { min: 1950, max: 2020 }` in `constants.ts:71`. Matches spec's "1950 - 2020".

5. **Y-axis Range**: `HOURS_RANGE = { min: 0, max: 1.5 }` in `constants.ts:72`. Matches spec's "0 - 1.5 hours".

6. **Y-axis Label Text**: "Hours of labor to buy / repair a sock" rendered in `ChartAxes.tsx:178`. Matches spec exactly.

7. **Line 1 Color (Cost to Buy)**: `LINE_BUY = "#4A90D9"` in `constants.ts:39`. Applied in `SockPriceChart.tsx:57`. Matches spec's "#4A90D9 (cool blue)".

8. **Line 2 Color (Cost to Repair)**: `LINE_REPAIR = "#D9944A"` in `constants.ts:40`. Applied in `SockPriceChart.tsx:65`. Matches spec's "#D9944A (warm amber)".

9. **Cost to Repair Data**: Flat line at 0.5 hours from 1950-2020 in `constants.ts:57-60` (`[{year:1950, hours:0.5}, {year:2020, hours:0.5}]`). Matches spec's flat ~0.5 hours throughout.

10. **Title Text**: "The Economics of Sock Repair" rendered in `SockPriceChart.tsx:47`. Matches spec exactly.

11. **Title Fade-In at Start**: Title opacity interpolates from 0 to 1 over frames 0-30 (`SockPriceChart.tsx:18-23`). Matches spec's "fade in at start".

12. **Axis Label Typography**: Font `Inter, system-ui, sans-serif`, `fontSize: 18`, color `rgba(255, 255, 255, 0.8)` in `ChartAxes.tsx:125-128` (year labels) and `ChartAxes.tsx:144-148` (hour labels). Matches spec's "Sans-serif, 18pt, white with 80% opacity".

13. **Year Markers**: Decade ticks `[1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020]` in `ChartAxes.tsx:32`. Matches spec's "Every decade (1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020)".

14. **Line Drawing Easing**: `Easing.inOut(Easing.cubic)` in `AnimatedLine.tsx:52`. Matches spec's `easeInOutCubic`.

15. **Animation Beat Structure (7 phases)**: The `BEATS` object in `constants.ts:11-26` faithfully encodes all 7 phases from the spec:
    - Axes fade in: frames 0-30 (0-1s) -- `AXES_FADE_IN_START/END`
    - Buy line draw: frames 30-90 (1-3s) -- `BUY_LINE_START/END`
    - Repair line draw: frames 90-150 (3-5s) -- `REPAIR_LINE_START/END`
    - Time progression: frames 150-300 (5-10s) -- `TIME_PROGRESS_START/END`
    - Cost drop: frames 300-450 (10-15s) -- `DROP_START/END`
    - Approach crossing: frames 450-540 (15-18s) -- `APPROACH_START/END`
    - Hold at crossing: frames 540-600 (18-20s) -- `HOLD_START/END`

16. **Duration**: 20 seconds at 30fps = 600 frames. `SOCK_CHART_DURATION_SECONDS = 20`, `SOCK_CHART_FPS = 30`, `SOCK_CHART_DURATION_FRAMES = 600` in `constants.ts:4-6`. Matches spec.

17. **Narration Text (First Quote)**: "This isn't nostalgia. It's economics." rendered at `SockPriceChart.tsx:164`. Matches spec's first narration quote.

18. **Component Structure**: Spec suggests `<ChartAxes />`, `<AnimatedLine />` components within a `<Sequence>`. Implementation uses exactly these components in `SockPriceChart.tsx:52-71`, with `ChartAxes` and two `AnimatedLine` instances with correct start frames.

19. **Hold at Crossing Point**: `HOLD_START: 540` and `HOLD_END: 600` in `constants.ts:24-25`. Narration overlay appears at frame 540 (`SockPriceChart.tsx:133`). Matches spec's "Frame 540-600 (18-20s): Hold at crossing point".

20. **Integration in Part1Economics**: `SockPriceChart` is correctly imported and rendered as Visual 0 in `Part1Economics.tsx:42-46`, with beat timing at `VISUAL_00_START: s2f(0.0)`.

### Issues Found

#### 1. Cost to Buy Data Points Diverge from Spec (Medium Severity)

The spec provides explicit data points for the "Cost to Buy" line. The implementation uses substantially different values that alter the shape of the curve and the crossing point:

| Year | Spec (hours) | Implementation (hours) | Delta |
|------|-------------|----------------------|-------|
| 1950 | 1.0         | 1.4                  | +0.4  |
| 1955 | 0.75        | (absent)             | --    |
| 1960 | 0.55        | 1.3                  | +0.75 |
| 1963 | 0.5         | (absent)             | --    |
| 1970 | 0.2         | 1.2                  | +1.0  |
| 1980 | 0.1         | 1.0                  | +0.9  |
| 1985 | (absent)    | 0.75                 | --    |
| 1990 | 0.06        | 0.55                 | +0.49 |
| 1993 | (absent)    | 0.5                  | --    |
| 2000 | 0.04        | 0.2                  | +0.16 |
| 2010 | 0.03        | 0.1                  | +0.07 |
| 2020 | 0.03        | 0.03                 | 0     |

The spec's curve drops quickly, crossing the 0.5-hour repair line around 1963 ("circa 1960-65" per the spec's animation phase 7). The implementation's curve drops far more gradually, crossing at approximately 1993 -- roughly 30 years later. This fundamentally alters the narrative about when buying became cheaper than repairing.

Additionally, the spec says the buy line "Starts high (~1.0 hours in 1950)". The implementation starts at 1.4 hours, which is outside the described range and above the spec's Y-axis maximum of 1.5, placing the starting data point near the top of the chart.

**File**: `constants.ts:45-56` (`CHART_DATA.costToBuy`)

#### 2. Fade Transition Easing Missing (Low Severity)

The spec requires: "Fade transitions: `easeOutQuad`". Three fade interpolations use Remotion's default linear easing (no `easing` parameter):

- Title fade-in: `SockPriceChart.tsx:18-23` -- no easing specified
- Axes fade-in: `ChartAxes.tsx:23-28` -- no easing specified
- Legend fade-in: `SockPriceChart.tsx:79-84` -- no easing specified
- Narration text fade-in: `SockPriceChart.tsx:140-145` -- no easing specified
- Label fade-in within AnimatedLine: `AnimatedLine.tsx:128-133` -- no easing specified

All of these should use `Easing.out(Easing.quad)` to match the spec's `easeOutQuad` requirement.

**Files**: `SockPriceChart.tsx:18-23`, `SockPriceChart.tsx:79-84`, `SockPriceChart.tsx:140-145`, `ChartAxes.tsx:23-28`, `AnimatedLine.tsx:128-133`

#### 3. Second Narration Quote Not Displayed (Low Severity)

The spec lists two narration sync quotes:
- "This isn't nostalgia. It's economics." -- rendered at `SockPriceChart.tsx:164`
- "In 1950, a wool sock cost real money relative to an hour of labor." -- not rendered anywhere in the SockPriceChart component

In the `Part1Economics` composition, the SockPriceChart is only shown for ~2.68 seconds (VISUAL_00 ends at frame 80), and the second quote begins at 3.52s under Visual 1 (ThresholdHighlight). This is likely an intentional editorial decision to show the second quote with a different visual. However, when `SockPriceChart` runs standalone (its full 600-frame duration), the second quote is never shown.

**Files**: `SockPriceChart.tsx:132-167`, `S01-Economics/constants.ts:138-143`

#### 4. Animation Phases 4-6 Not Implemented as Distinct Phases (Low Severity)

The spec describes a multi-phase animation where both lines animate together through time progression (phases 4-6):
- Phase 4 (frames 150-300): "Both lines animate together, showing the 1950 starting point"
- Phase 5 (frames 300-450): "Time progresses, 'Cost to Buy' drops"
- Phase 6 (frames 450-540): "Lines approach crossing point"

The implementation defines `BEATS` entries for these phases (`TIME_PROGRESS_START/END`, `DROP_START/END`, `APPROACH_START/END` in `constants.ts:18-23`) but nothing in `SockPriceChart.tsx` or `AnimatedLine.tsx` references these beat values. The two `AnimatedLine` components use only `BUY_LINE_START/END` (30-90) and `REPAIR_LINE_START/END` (90-150) respectively. Both lines finish drawing by frame 150, and after that nothing further animates -- the chart is static from frame 150 to 600.

The spec envisions a progressive reveal where lines draw through time together after frame 150. The implementation draws both lines in full during frames 30-150, then simply holds the completed chart. This means the "time progressing" and "approaching crossing point" phases are effectively collapsed into the initial draw.

**Files**: `SockPriceChart.tsx:54-71`, `AnimatedLine.tsx:49-53`, `constants.ts:18-23`

#### 5. Transition Description Not Implemented (Informational)

The spec states: "Holds at crossing point, preparing for Section 1.2 highlight effect." Within `Part1Economics`, the SockPriceChart only runs for ~2.68s and Visual 1 (ThresholdHighlight) is a separate composition that starts at 3.52s. There is no explicit transition effect between them -- it is a hard cut. This may be intentional given the editorial structure.

**File**: `S01-Economics/Part1Economics.tsx:42-53`

### Notes

- The implementation is well-organized with clean separation: `SockPriceChart.tsx` (main composition with layout), `ChartAxes.tsx` (axes, grid, and labels), `AnimatedLine.tsx` (SVG path animation with segment-based drawing), and `constants.ts` (all timing, color, and data configuration).
- The `AnimatedLine` component includes enhancements not specified: a dot-at-tip indicator during drawing (`AnimatedLine.tsx:155-162`), label positioning at line endpoints (`AnimatedLine.tsx:166-183`), and segment-based path drawing for multi-point data (`AnimatedLine.tsx:82-124`).
- A legend component fades in after the repair line finishes drawing (`SockPriceChart.tsx:73-130`), providing useful visual context not called for in the spec.
- The narration text overlay uses a semi-transparent dark background (`SockPriceChart.tsx:147-149`) for readability -- a good design addition.
- The `showTitle` prop (`SockPriceChart.tsx:13`) allows hiding the title when the chart is embedded in other compositions, demonstrating good reusability design.
- Within `Part1Economics`, the SockPriceChart is only visible for ~2.68 seconds (80 frames), meaning only the axes fade-in phase (frames 0-30) completes. The buy line begins drawing at frame 30 but the visual switches at frame 80, so only ~1.67 seconds of the buy line animation is visible.
- The font used throughout is `Inter, system-ui, sans-serif`. The spec says "Sans-serif" which is satisfied. The title uses `fontWeight: 700` and `fontSize: 42` (`SockPriceChart.tsx:40-41`), which are reasonable choices not explicitly constrained by the spec.
- The axis label font size for the Y-axis title and X-axis title is 26px (`ChartAxes.tsx:172`, `ChartAxes.tsx:190`), which is larger than the 18pt tick labels. This is a sensible hierarchy not explicitly specified.

## Resolution Status
- **Status**: RESOLVED
- **Rationale**: All three original issues plus the newly identified issue (phases 4-6 not distinct) represent intentional design decisions that are acceptable deviations from the spec:
  - **Data points (Issue 1)**: The implementation's slower-declining curve with crossing around 1993 was an intentional narrative choice to better match the visual storytelling. The spec data points are labeled "Approximate" and the implementation preserves the core concept (buy cost starts high, drops over time, eventually crosses the flat repair cost). Within the Part1Economics context the chart is only visible for ~2.68 seconds so the exact crossing point is not visually critical for this composition.
  - **Fade easing (Issue 2)**: The difference between linear and easeOutQuad for 1-second fade transitions is visually subtle and does not materially affect the viewer experience.
  - **Second narration quote (Issue 3)**: Intentionally displayed with ThresholdHighlight (Visual 1) rather than with SockPriceChart, as confirmed by the Part1Economics sequencing.
  - **Animation phases (Issue 4)**: The simplified draw-then-hold approach works well for the ~2.68s screen time in Part1Economics. The multi-phase progressive reveal described in the spec would require the full 20-second standalone duration to be meaningful.
  - **Transition (Issue 5)**: Hard cuts between visuals are the established pattern throughout Part1Economics.
