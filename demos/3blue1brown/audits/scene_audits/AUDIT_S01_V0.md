# Scene Audit: S01 Part 1 Economics - V0 SockPriceChart

**Video:** `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/outputs/sections/part1_economics.mp4`
**Time range:** 0.0s - 2.68s
**Script visual:** "Price chart animation. 1950: A pair of quality wool socks costs about an hour of wages. Graph shows labor cost vs garment cost over time."
**Narration:** "This isn't nostalgia. It's economics."
**Spec:** `specs/01-economics/01_sock_price_chart.md`
**Date:** 2026-02-09

## Frames Examined

- t=0s: Dark background (#1a1a2e area). Nearly entirely dark with a very faint horizontal line or gradient band visible in the upper third of the frame. No chart elements, no title, no axes visible yet. This is the opening fade-in frame -- the chart has not yet appeared.

- t=1s: **Axes and chart structure fully visible.**
  - Title: "The Economics of Sock Repair" displayed at top center in bold white sans-serif text. Clearly readable.
  - X-axis: "Year" label at bottom center. Year markers: 1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020 -- all visible along bottom axis. Matches spec exactly.
  - Y-axis: "Hours of labor to buy / repair a sock" label rotated vertically on left side. Y-axis values: 0, 0.5, 1, 1.5 -- visible. Matches spec (range 0-1.5 hours).
  - Grid lines: Subtle dashed horizontal and vertical grid lines visible in gray -- matches spec's "#333344 dashed" description.
  - Background: Dark navy (#1a1a2e) -- matches spec.
  - No data lines drawn yet -- just the axes and grid. This matches the spec's timing: axes fade in during frames 0-30 (0-1s).

- t=2s: **One data line drawing in progress.**
  - A light blue line (consistent with #4A90D9 cool blue) is being drawn from left to right.
  - The line starts at approximately 1.4 hours at 1950, drops gradually to ~1.2 at 1970, then descends more steeply to ~1.0 at 1980, and continues dropping sharply. The drawing head/endpoint appears to be around the 1985 area at approximately 0.7 hours, with a small circular dot at the leading edge.
  - Only ONE line is visible -- this is the "Cost to Buy" line. The "Cost to Repair" amber line has not appeared yet.
  - The line trajectory shows the expected downward trend from left to right -- sock prices dropping over time.

## Detailed Element Verification

### 1. Dark Background (#1a1a2e) with Subtle Gradient
**VERIFIED.** The background is dark navy, consistent with #1a1a2e. A very subtle gradient may be present (slightly lighter at top, darker at bottom) but the overall tone is correct.

### 2. Chart Title: "The Economics of Sock Repair"
**VERIFIED.** Present at top center in bold white sans-serif. Clearly readable. Matches spec.

### 3. X-axis: Years (1950-2020)
**VERIFIED.** All 8 decade markers visible: 1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020. "Year" axis label at bottom center.

### 4. Y-axis: "Hours of labor to buy / repair a sock"
**VERIFIED.** Rotated vertical label on left side. Values 0, 0.5, 1, 1.5 marked. Range matches spec (0-1.5 hours).

### 5. Grid Lines
**VERIFIED.** Subtle dashed gray grid lines visible for both horizontal (at 0.5, 1.0, 1.5 values) and vertical (at each decade) guides. Color appears consistent with spec's #333344.

### 6. Line 1 (Cost to Buy) -- Cool Blue (#4A90D9)
**PARTIALLY VERIFIED (in progress).** At t=2s, a light blue line is drawing from left to right. The color appears consistent with cool blue (#4A90D9). The line is progressing through the timeline. However:

**DATA ISSUE:** The line starts at approximately **1.4 hours** at 1950, not the spec's **1.0 hours**. The spec's data table shows `{"year": 1950, "hours": 1.0}` but the rendered line begins well above the 1.0 gridline, closer to 1.4-1.5. This is a significant discrepancy in the starting data point.

Additionally, the curve's shape shows a gradual decline from 1950-1970 before steepening, which broadly matches the spec data (1.0 -> 0.75 -> 0.55 by 1960) but is offset higher by ~0.4 hours across all early data points.

### 7. Line 2 (Cost to Repair) -- Warm Amber (#D9944A)
**NOT YET VISIBLE.** At t=2s (the latest frame in this segment), only one line is present. Per the spec's animation sequence, the repair cost line begins drawing at frame 90 (3s), so it would not appear within this 2.68s segment. This is expected timing behavior, not an issue.

### 8. Animation Timing
**VERIFIED (axes phase).** The animation sequence matches spec:
- t=0s: Fade-in from dark (frame 0) -- correct
- t=1s: Axes fully visible with labels, title, grid -- matches spec's "Frame 0-30: Axes fade in with labels"
- t=2s: Cost to Buy line drawing from left to right -- matches spec's "Frame 30-90: Cost to Buy line draws"

## Assessment

### Matches Script
- "Price chart animation" -- VERIFIED. Animated chart with axes and line drawing.
- "1950: A pair of quality wool socks costs about an hour of wages" -- PARTIALLY. The 1950 starting point shows ~1.4 hours, not ~1.0 hours as stated in the spec data. The script says "about an hour" which is closer to 1.0 than 1.4.
- "Graph shows labor cost vs garment cost over time" -- VERIFIED. The chart structure with year on X and labor hours on Y conveys this.
- Chart title "The Economics of Sock Repair" -- VERIFIED.
- Dark background, grid, axes -- all VERIFIED.

### Issues Found
| # | Severity | Description | Fix Suggestion |
|---|----------|-------------|----------------|
| 1 | MAJOR | The "Cost to Buy" line starts at approximately **1.4 hours** at 1950, but the spec's data table specifies **1.0 hours** as the 1950 starting value. The script narration says "about an hour of wages." The rendered line begins well above the 1.0 gridline marker, closer to the 1.5 maximum. This data discrepancy changes the visual narrative -- the crossing point with the repair cost line (at 0.5 hours) would occur at a different year than the spec's 1960-65 target. | Adjust the "Cost to Buy" data so the 1950 starting point is at 1.0 hours, matching the spec's data table and the narration. This will also ensure the crossing point with the repair cost line occurs at the correct ~1960-65 position. |
| 2 | MINOR | At t=2s, the leading edge of the drawing line has a small circular dot (data point marker) at the endpoint. The spec does not mention data point markers -- it describes clean line drawing with easeInOutCubic. | Cosmetic -- the dot serves as a visual indicator of the animation progress. Could be removed if clean line drawing is preferred, but does not significantly impact readability. |

## Status: NEEDS_FIX

**Rationale:** The chart structure, styling, and animation timing are well-executed -- dark background, correct title, proper axes with labels, grid lines, and smooth line drawing animation. However, the "Cost to Buy" line starting value is a MAJOR data issue. The spec says 1.0 hours at 1950 and the narration says "about an hour of wages," but the rendered line starts at approximately 1.4 hours. This data offset will cascade to an incorrect crossing point with the repair cost line, which is a key narrative beat in the economics argument. The starting data point needs to be corrected to match the spec.
