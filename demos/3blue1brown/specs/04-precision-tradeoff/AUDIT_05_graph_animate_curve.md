# Audit: 05_graph_animate_curve.md

## Spec Summary
An animation showing a marker traveling along an inverse curve from left to right, with a large prompt icon that shrinks and test walls that multiply. The marker should have a subtle trail effect, and the entire animation emphasizes the precision tradeoff: few tests require detailed prompts, many tests allow simpler prompts.

## Implementation Status
Implemented

## Deltas Found

### Marker position calculation differs
- **Spec says**: `markerX = 100 + curveProgress * 1300` and `markerY = 650 - 500 * (1 / (curveProgress * 2 + 0.3))`
- **Implementation does**: `markerX = 200 + curveProgress * 1100` (line 303) and `markerY = 700 - 450 * (1 / (curveProgress * 2 + 0.3))` (line 304)
- **Severity**: Medium - Different scale/positioning but mathematically similar curve

### Trail points calculation differs
- **Spec says**: `const trailX = 100 + trailProgress * 1300` and `const trailY = 650 - 500 * (1 / (trailProgress * 2 + 0.3))`
- **Implementation does**: `const trailX = 200 + trailProgress * 1100` (line 16) and `const trailY = 700 - 450 * (1 / (trailProgress * 2 + 0.3))` (line 17)
- **Severity**: Low - Matches the main marker's different coordinates

### Prompt icon positioning differs
- **Spec says**: `position={{ x: 250, y: 400 }}` (line 138 in spec)
- **Implementation does**: `position={{ x: 300, y: 400 }}` (line 330)
- **Severity**: Low - 50px horizontal shift

### Test walls positioning differs
- **Spec says**: `position={{ x: 1200, y: 400 }}` (line 144 in spec)
- **Implementation does**: `position={{ x: 1550, y: 400 }}` (line 336)
- **Severity**: Low - 350px horizontal shift

### Position label positioning differs
- **Spec says**: Uses `position` prop with string values "left" and "right"
- **Implementation does**: Uses `positionSide` prop instead (line 171)
- **Severity**: Low - Different prop name but same functionality

### Position label positioning values
- **Spec says**: No specific x coordinates mentioned in component
- **Implementation does**: `x = positionSide === "left" ? 300 : 1620` (line 175)
- **Severity**: Low - Implementation provides specific values not in spec

### Fixed line widths vs random
- **Spec says**: `width: ${60 + Math.random() * 30}%` for prompt lines (line 262)
- **Implementation does**: Fixed array `const lineWidths = [85, 70, 90, 65, 80, 75, 85, 60];` (line 71)
- **Severity**: Low - Fixed values prevent re-render flickering

### Transform origin on prompt/walls
- **Spec says**: `transformOrigin: 'center'` (lines 234, 290)
- **Implementation does**: `transform: translate(-50%, -50%) scale(${scale})` with `transformOrigin: "center"` (lines 79, 145)
- **Severity**: Low - Implementation adds translate for proper centering

### Setup phase animation added
- **Spec says**: Animation starts at frame 0 with marker appearing
- **Implementation does**: Adds setup opacity fade-in from frames 0-60 (lines 283-288)
- **Severity**: Low - Enhancement not in spec

### Final pulse timing differs
- **Spec says**: `const finalPulse = frame > 300 ? ...` (line 120)
- **Implementation does**: `const finalPulse = frame > BEATS.ARRIVE_START ? ...` (line 314)
- **Severity**: Low - Uses constant instead of magic number

### Title element added
- **Spec says**: No title mentioned
- **Implementation does**: Adds "The Precision Tradeoff" title at top (lines 357-376)
- **Severity**: Low - Enhancement not in spec

### showLabels prop added
- **Spec says**: Labels always shown
- **Implementation does**: Conditional rendering with `showLabels` prop (lines 341-354)
- **Severity**: Low - Flexibility enhancement

## Missing Elements
None - all spec requirements are present in the implementation, though with some coordinate/scale adjustments.

## Additional Features
1. Setup opacity animation for smoother entrance
2. Title display at top of screen
3. Optional label display via `showLabels` prop
4. Uses BEATS constants from external constants file for frame timing
5. Uses COLORS constants for color values
