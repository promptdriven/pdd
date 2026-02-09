# Audit: Sock Price Chart (01_sock_price_chart.md)

## Status: ISSUES FOUND

### Requirements Met

- **Canvas Resolution**: 1920x1080 correctly defined in `constants.ts` (`SOCK_CHART_WIDTH = 1920`, `SOCK_CHART_HEIGHT = 1080`).
- **Background**: Dark `#1a1a2e` with subtle gradient to `#0f0f1a` applied via `linear-gradient` in `SockPriceChart.tsx:28`. Matches spec.
- **Grid Lines**: Color `#333344` (`COLORS.GRID`) with `strokeDasharray="5,5"` in `ChartAxes.tsx:76`. Matches spec's "subtle gray, dashed".
- **X-axis Range**: `YEAR_RANGE = { min: 1950, max: 2020 }` in `constants.ts:71`. Year ticks `[1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020]` in `ChartAxes.tsx:32`. Matches spec exactly.
- **Y-axis Range**: `HOURS_RANGE = { min: 0, max: 1.5 }` in `constants.ts:72`. Hour ticks `[0, 0.5, 1, 1.5]` in `ChartAxes.tsx:33`. Matches spec.
- **Y-axis Label**: "Hours of labor to buy / repair a sock" in `ChartAxes.tsx:178`. Matches spec.
- **Line Colors**: `LINE_BUY = "#4A90D9"` (cool blue) and `LINE_REPAIR = "#D9944A"` (warm amber) in `constants.ts:39-40`. Match spec exactly.
- **Cost to Repair Data**: Flat line at 0.5 hours from 1950 to 2020 (`constants.ts:57-60`). Matches spec.
- **Title**: "The Economics of Sock Repair" in `SockPriceChart.tsx:47`. Matches spec.
- **Axis Label Typography**: Inter/sans-serif, fontSize 18, color `rgba(255, 255, 255, 0.8)` in `ChartAxes.tsx:125-128`. Matches spec's "Sans-serif, 18pt, white with 80% opacity".
- **Easing (Line Drawing)**: `Easing.inOut(Easing.cubic)` in `AnimatedLine.tsx:52`. Matches spec's `easeInOutCubic`.
- **Animation Beat Structure**: The 7-phase timing from the spec (axes fade 0-30, buy line 30-90, repair line 90-150, time progress 150-300, drop 300-450, approach 450-540, hold 540-600) is exactly reproduced in `BEATS` object (`constants.ts:11-26`).
- **Duration**: 20 seconds / 600 frames at 30fps (`constants.ts:4-6`). Matches spec.
- **Narration Text**: "This isn't nostalgia. It's economics." displayed at `SockPriceChart.tsx:164`. Matches spec.

### Issues Found

#### 1. Cost to Buy Data Points Diverge from Spec (Medium Severity)

The spec provides explicit data points for the "Cost to Buy" line, but the implementation uses significantly different values:

| Year | Spec (hours) | Implementation (hours) |
|------|-------------|----------------------|
| 1950 | 1.0         | 1.4                  |
| 1955 | 0.75        | (not present)        |
| 1960 | 0.55        | 1.3                  |
| 1963 | 0.5         | (not present)        |
| 1970 | 0.2         | 1.2                  |
| 1980 | 0.1         | 1.0                  |
| 1985 | (not present) | 0.75               |
| 1990 | 0.06        | 0.55                 |
| 1993 | (not present) | 0.5                 |
| 2000 | 0.04        | 0.2                  |
| 2010 | 0.03        | 0.1                  |
| 2020 | 0.03        | 0.03                 |

The implementation's curve starts much higher (1.4 vs 1.0 hours) and drops much more slowly. In the spec, the crossing point with the repair line (0.5 hours) occurs around 1963. In the implementation, the crossing point occurs around 1993 -- roughly 30 years later. This fundamentally changes the narrative about when buying became cheaper than repairing.

**File**: `constants.ts:45-56` (`CHART_DATA.costToBuy`)

#### 2. Fade Transition Easing Not Applied (Low Severity)

The spec requires fade transitions to use `easeOutQuad`. The title fade-in (`SockPriceChart.tsx:18-23`) and axes fade-in (`ChartAxes.tsx:23-28`) both use Remotion's default linear interpolation (no `easing` option provided). Only the line drawing animation correctly applies a custom easing function.

**Files**: `SockPriceChart.tsx:18-23`, `ChartAxes.tsx:23-28`

#### 3. Second Narration Quote Not Displayed (Low Severity)

The spec lists two narration quotes for this section:
- "This isn't nostalgia. It's economics." -- present in implementation
- "In 1950, a wool sock cost real money relative to an hour of labor." -- not displayed

In the `Part1Economics` composition, the SockPriceChart is only shown for approximately 2.68 seconds (VISUAL_00_START to VISUAL_00_END), and the second quote begins at 3.52 seconds under a different visual (ThresholdHighlight). This is likely an intentional editorial choice where the second quote accompanies a different visual, but it means the SockPriceChart's hold phase (frames 540-600) is never reached in the Part1Economics context.

**Files**: `SockPriceChart.tsx:132-167`, `S01-Economics/constants.ts:138-139`

### Notes

- The implementation is well-structured with clean component separation: `SockPriceChart.tsx` (main composition), `ChartAxes.tsx` (axes/grid/labels), `AnimatedLine.tsx` (animated path drawing), and `constants.ts` (all configuration).
- The `BEATS` timing system in `constants.ts` faithfully reproduces all 7 animation phases from the spec with exact frame numbers.
- The `AnimatedLine` component includes a nice dot-at-tip effect during drawing and label fade-in that are not specified but enhance the visual.
- A legend component fades in after the repair line finishes drawing (`SockPriceChart.tsx:73-130`) -- a useful UX addition not in the spec.
- The `SockPriceChart` is designed as a standalone 20-second composition but within `Part1Economics` it is only displayed for the first ~2.68 seconds. The internal BEATS system still controls animation timing from frame 0, meaning only the axes fade-in phase (0-30 frames / 0-1 second) is visible in the Part1Economics context.
- The `showTitle` prop allows the title to be toggled, useful for when the chart is reused in other compositions.
- The font weight of 700 (bold) on the title (`SockPriceChart.tsx:41`) is a reasonable design choice not explicitly specified.

## Resolution Status
- **Status**: UNRESOLVED
- **Primary Blocker**: The costToBuy data points in `constants.ts:45-56` significantly diverge from the spec's data, shifting the crossing point from ~1963 to ~1993. This changes the core narrative message of the chart. Needs to be reconciled -- either the spec data should be updated to match the implementation's intended narrative, or the implementation data should be corrected to match the spec.
