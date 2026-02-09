# Audit: 03_lines_diverge.md

## Spec Summary
A 15-second sequence showing the dramatic divergence of sock costs from 1965 to 2020. The "Cost to Buy" line drops to near-zero while "Cost to Repair" stays flat. Includes a year counter, shaded "irrational zone", gap indicator, and zoom-out effect.

## Implementation Status
**Implemented**

## Deltas Found

### Year Counter Font
- **Spec says**: "Monospace or digital-style font, 48pt" (line 60)
- **Implementation does**: Uses "'JetBrains Mono', monospace" with fontSize: 48 in YearCounter.tsx:36-38
- **Severity**: None - JetBrains Mono is an excellent monospace choice

### Year Counter Pulse Effect
- **Spec says**: No specific pulse effect mentioned
- **Implementation does**: Adds subtle sine-wave pulse when year changes (YearCounter.tsx:27)
- **Severity**: Low - Nice polish addition not in spec

### Shaded Region Label
- **Spec says**: "Light red/amber fill at 10% opacity" with label "Darning is irrational" (lines 36-37)
- **Implementation does**: Uses gradient fill (COLORS.LINE_REPAIR at 30% to 10%) with stripe pattern overlay in ShadedRegion.tsx:131-154
- **Severity**: Low - Implementation adds visual texture beyond spec

### Gap Indicator Timing
- **Spec says**: "Gap indicator appears" around Frame 180-270 (line 46)
- **Implementation does**: Uses BEATS.GAP_INDICATOR_START/END in GapIndicator.tsx:36-45
- **Severity**: Low - Exact timing may differ but structure matches

### Gap Indicator Position
- **Spec says**: "Position the gap indicator at a fixed year (e.g., 2000) or current year" (line 71)
- **Implementation does**: Fixed at year 2000 in GapIndicator.tsx:72
- **Severity**: None - Implementation follows spec suggestion

### Gap Value Display
- **Spec says**: Label showing "Waste of time" or arrow indicating irrational zone (line 32)
- **Implementation does**: Shows "{gapValue}h saved" (e.g., "0.47h saved") in GapIndicator.tsx:206
- **Severity**: Medium - Different messaging approach, more data-focused than emotional

### Arrow Markers
- **Spec says**: No detailed arrow specification
- **Implementation does**: Double-ended arrow with SVG markers (arrowUp/arrowDown) in GapIndicator.tsx:110-135
- **Severity**: Low - Good implementation detail

### Zoom Out Effect
- **Spec says**: "Frame 360-450 (12-15s): Zoom out slightly to show full picture" (line 48)
- **Implementation does**: Zoom from scale 1 to 0.95 in LinesDiverge.tsx:59-67
- **Severity**: Low - Implementation zooms out (0.95 is smaller), which is opposite of "show full picture" but may be intended to show more context

### Frozen Chart Portion
- **Spec says**: Chart continues from threshold marker fading to 50% (line 40)
- **Implementation does**: Builds path from costToBuyUntil1963 data and animates from 1963 onward in LinesDiverge.tsx:71-104
- **Severity**: None - Correct approach to continue animation from previous state

### Year Label Font Size
- **Spec says**: No size mentioned (inherits from previous sections)
- **Implementation does**: fontSize: 28 in LinesDiverge.tsx:274
- **Severity**: Low - Larger than Section 1.1 (18pt), may be for better readability

## Missing Elements

### Data Visualization Table
- **Spec provides**: Detailed data points showing cost progression (lines 50-55)
- **Implementation**: Uses CHART_DATA constants (not read)
- **Severity**: Unknown - Cannot verify data accuracy

### Shaded Region Border
- **Spec says**: No explicit border mentioned
- **Implementation does**: Adds dashed border to shaded region (ShadedRegion.tsx:156-164)
- **Severity**: None - Good visual enhancement

## Notes
- The implementation properly continues the animation from the threshold state
- The year counter is well-implemented with smooth progression
- The shaded region uses gradient and pattern fills for visual richness
- The gap indicator is data-driven (shows actual hour difference) rather than emotional messaging
- The zoom effect direction seems reversed from spec intent but may be correct for showing "full picture"
