# Audit: 02_threshold_highlight.md

## Spec Summary
A 10-second sequence that highlights the crossing point from the previous chart with a pulsing marker, label reading "The Threshold", and three pulse wave effects. The chart from Section 1.1 remains visible but frozen.

## Implementation Status
**Implemented**

## Deltas Found

### Pulse Duration and Timing
- **Spec says**: Three distinct pulses at specific frames: Frame 30-90 (first), 90-150 (second), 150-210 (third) (lines 38-42)
- **Implementation does**: Uses BEATS constants for PULSE_1_START/END, PULSE_2_START/END, PULSE_3_START/END in CrossingPointMarker.tsx:49-56
- **Severity**: Low - Timing may differ but structure matches spec intent

### Spring Configuration
- **Spec says**: Circle growth uses `spring({ damping: 15 })` (line 46)
- **Implementation does**: Uses `damping: 15, stiffness: 100` in CrossingPointMarker.tsx:22-23
- **Severity**: Low - Implementation adds stiffness parameter for more control

### Label Connector Line Style
- **Spec says**: Connector line from label to point (line 29)
- **Implementation does**: Dashed line with strokeDasharray="6,4" in AnimatedLabel.tsx:70
- **Severity**: None - Dashed style is appropriate

### Label Position Offset
- **Spec says**: "Above and right of crossing point" (line 27)
- **Implementation does**: Uses offsetX={120}, offsetY={-80} in ThresholdHighlight.tsx:92-93
- **Severity**: None - Specific pixel values implement the directional guidance

### Pulse Wave Easing
- **Spec says**: Pulse waves use `easeOutQuad` with opacity decay (line 48)
- **Implementation does**: Custom interpolation function in CrossingPointMarker.tsx:28-36 with manual opacity curve [0, 0.6, 0]
- **Severity**: Low - Implementation achieves similar visual effect

### Hold Phase Pulse
- **Spec says**: Three pulses, then "Hold, pulses continue subtly" (line 43)
- **Implementation does**: Continuous subtle pulse during hold phase using sine wave (CrossingPointMarker.tsx:59-62)
- **Severity**: None - Good implementation of "continue subtly"

### Chart Year Range Mismatch
- **Spec says**: Chart continues from Section 1.1 (1950-2020)
- **Implementation does**: FrozenChart.tsx:46 shows yearTicks = [1920, 1930, 1940, 1950, 1960, 1970, 1980, 1990]
- **Severity**: Medium - Year range starts earlier than spec (inherited from Section 1.1 delta)

### Narration Position
- **Spec says**: No specific position mentioned
- **Implementation does**: Positioned at top: "18%" in ThresholdHighlight.tsx:155
- **Severity**: Low - Reasonable implementation choice to avoid obscuring chart

### Glow Filter Implementation
- **Spec says**: "Pulsing glow effect (amber #D9944A at 50% opacity)" (line 23)
- **Implementation does**: Uses SVG filter with feGaussianBlur and radial gradient in CrossingPointMarker.tsx:72-87
- **Severity**: None - Correct implementation technique for glow

## Missing Elements

### Connector Line Animation Detail
- **Spec mentions**: "Connector line from label to point" but no timing details
- **Implementation**: Connector line draws in with separate animation (AnimatedLabel.tsx:35-44)
- **Severity**: None - Good addition for polish

## Notes
- The implementation properly freezes the previous chart state using FrozenChart component
- The three pulse waves are distinct and timed, matching spec intent
- The subtle hold phase pulse is a nice touch that extends the animation naturally
- Color constants (COLORS.PULSE_GLOW, COLORS.MARKER) are assumed to match spec colors

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**:
  - Fixed YEAR_RANGE in constants.ts from (1920-1990) to (1950-2020) to match Section 1.1 spec
  - Updated CHART_DATA.costToBuy to include data points from 1950-2020 (added 2000, 2010, 2020; removed 1920, 1930, 1940)
  - Updated CHART_DATA.costToRepair year range from (1920-1990) to (1950-2020)
  - Fixed yearTicks in FrozenChart.tsx from [1920, 1930, 1940, 1950, 1960, 1970, 1980, 1990] to [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020]
- **Remaining Issues**: None - All HIGH and MEDIUM severity deltas have been resolved
