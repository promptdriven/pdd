# Audit: 13_pie_to_curve.md

## Spec Summary
A 10-second (300 frames) visualization showing a pie chart morphing into an exponential cost curve with a flat regeneration line. The pie chart rotates and flattens into chart axes, then two curves appear: an exponential "Technical debt" curve (amber) showing compound growth, and a flat "Regeneration cost" line (blue) showing debt reset. The divergence between these lines is the visual argument for PDD.

## Implementation Status
**Implemented** - All core requirements are present with high fidelity to the spec.

## Deltas Found

### Morph Duration
- **Spec says**: "Frame 0-90 (0-3s): Morph begins"
- **Implementation does**: Uses BEATS.MORPH_START to BEATS.MORPH_END (need to verify this is frames 0-90)
- **Severity**: Low (need to verify constants match spec timing)
- **File reference**: PieToCurve.tsx:30-38

### Pie Segment Angles
- **Spec says**: Not specified in detail, but should morph from the pie chart in section 1.11
- **Implementation does**: Uses -60° to 60° for amber (120° total), 60° to 180° for blue (120° total), plus gray background
- **Severity**: Low (includes 3 segments instead of 2, angles differ from expected 15%/85% split)
- **File reference**: PieToCurve.tsx:220-243

### Axes Arrow Implementation
- **Spec says**: Not explicitly specified
- **Implementation does**: Adds arrow heads to both X and Y axes at frame BEATS.AXES_END
- **Severity**: None (enhancement that improves clarity)
- **File reference**: PieToCurve.tsx:316-334

### Exponential Curve Formula
- **Spec says**: "y = e^(0.3x) scaled" with base = 1.35 (~35% YoY growth)
- **Implementation does**: Uses COST_CURVE_DATA from constants with data points specified in spec (1.0, 1.35, 1.82, etc.)
- **Severity**: None (matches spec data exactly)
- **File reference**: PieToCurve.tsx references constants, ExponentialCurve.tsx:58-108

### Curve Drawing Easing
- **Spec says**: "Curve drawing: `easeOutQuad`"
- **Implementation does**: Uses `Easing.out(Easing.quad)` which is correct
- **Severity**: None (correctly implemented)
- **File reference**: ExponentialCurve.tsx:51-55

### Label Text Format
- **Spec says**: "Technical debt follows compound interest: Debt x (1 + Rate)^Time"
- **Implementation does**: "Technical debt follows compound interest:" with formula on next line as "Debt x (1 + Rate)^Time"
- **Severity**: None (matches spec, just formatted across two lines)
- **File reference**: PieToCurve.tsx:464-468

### Regeneration Label Position
- **Spec says**: Label should appear "near the flat line"
- **Implementation does**: Positions label at `regenY - 35` (35px above the line) on the right side
- **Severity**: None (implemented appropriately)
- **File reference**: PieToCurve.tsx:528-541

### Final Quote Text
- **Spec says**: Spec narration says "Unless you regenerate. Then the debt resets."
- **Implementation does**: Shows exact quote with quotation marks in italic Georgia serif font
- **Severity**: None (well implemented)
- **File reference**: PieToCurve.tsx:562

### Linear Reference Line
- **Spec says**: Not explicitly mentioned in this spec (may be from earlier version)
- **Implementation does**: Includes optional `showLinearRef` prop that displays a dashed blue "Linear" reference line
- **Severity**: None (optional enhancement, defaults to true)
- **File reference**: PieToCurve.tsx:15, ExponentialCurve.tsx:175-197

## Missing Elements

None identified. All major spec requirements are implemented:
- Pie chart morph animation (rotation, flattening, fade out)
- Axes establishment with grid lines
- X-axis label "Time (Years 1-10)"
- Y-axis label "Cumulative Maintenance Cost"
- Exponential curve drawing with compound interest formula label
- Flat regeneration line with "debt resets each cycle" label
- Color continuity (amber from pie to curve)
- Pulse animation on steep portion of curve
- Final state text quote
- Proper easing functions throughout

## Implementation Strengths

1. **Smooth morphing**: Complex morph animation with pie center movement, radius changes, rotation, and opacity fade
2. **Grid system**: Comprehensive grid lines for both horizontal and vertical axes with proper opacity control
3. **Axis labels**: Full implementation of tick labels for both axes with proper positioning
4. **Curve rendering**: Smooth bezier curve implementation using quadratic curves for exponential appearance
5. **Animated drawing**: Progressive curve drawing with animated dot at the tip
6. **Glow effects**: Visual enhancement with glow layers on regeneration line
7. **Pulse effect**: Proper pulse animation on the exponential curve during final phase
8. **Typography hierarchy**: Proper font sizing and styling for all labels and text elements
9. **Linear reference**: Optional reference line helps viewer understand the exponential nature

## Recommendations

1. Verify BEATS constants in constants.ts match spec timing exactly:
   - MORPH: 0-90 frames
   - AXES: 90-150 frames
   - CURVE: 150-210 frames
   - REGEN_LINE: 210-260 frames
   - FINAL: 260-300 frames
2. Consider adjusting pie segment angles to match the 15%/85% split from section 1.11 instead of using three equal segments
3. Verify the gray background segment is needed or if only amber and blue should appear
4. Otherwise, implementation is excellent and faithful to the spec

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**:
  - Verified BEATS constants in constants.ts - all timing matches spec exactly (0-90, 90-150, 150-210, 210-260, 260-300 frames)
  - Confirmed all core requirements are implemented correctly
  - No HIGH or MEDIUM severity issues found - all deltas were Low or None severity
- **Remaining Issues**:
  - Low severity items remain as design decisions (pie segment angles use 120° segments instead of 15%/85% split, includes gray background segment)
  - These are implementation choices that don't affect functionality and may be addressed in future refinements if needed
