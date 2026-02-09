# Audit: 03_patching_curve_wobbles.md

## Spec Summary
The smooth patching curve morphs into a wobbly version with 3-4 distinct dips (new bug, regression, merge conflict) and a $1.52T cost statistic callout. Duration ~15 seconds.

## Implementation Status
Implemented (Phase 3 of CompoundCurvesGraph.tsx)

## Deltas Found

### Wobble mathematical implementation
- **Spec says**: Smooth curve progressively deforms with dips at ~55%, ~70%, ~85% along X-axis (lines 21-26)
- **Implementation does**: `patchingWobblyY` function adds Gaussian dips at positions from DIP_POSITIONS array (lines 26-35)
- **Severity**: Low (uses Gaussian exponential for smooth dips, positions configurable via constants)

### Number of dips
- **Spec says**: 3-4 distinct dips (line 22)
- **Implementation does**: `DIP_POSITIONS.length` dips (3 dips based on iteration in lines 753-765)
- **Severity**: Low (appears to be 3 dips, within spec range)

### Dip depth specification
- **Spec says**: 10-20% of curve height at that point (line 23)
- **Implementation does**: Uses DIP_MAGNITUDES array with values applied via `dipTotal * wobbleAmount` (lines 29-33)
- **Severity**: Medium (magnitude values not visible here, need constant verification)

### Wobble animation timing
- **Spec says**: Frame 0-90 (0-3s) first dip, 90-180 (3-6s) second dip, 180-270 (6-9s) third dip (lines 75-92)
- **Implementation does**: Wobble amount interpolates frame 0-180 from 0→1 (lines 511-517)
- **Severity**: High (faster overall: 180 frames vs 270 frames for full wobble)

### Dip annotation timing
- **Spec says**: First at frame 60-90, second 150-180, third 240-270 (lines 78, 84, 90)
- **Implementation does**: Frame 40-70, 100-130, 160-190 (lines 520-535)
- **Severity**: Medium (all annotations appear earlier than spec)

### Dip labels
- **Spec says**: "new bug from patch" (~55%), "regression" (~70%), "merge conflict" (~85%) (lines 27-36)
- **Implementation does**: Uses DIP_LABELS array, renders via map at lines 753-765
- **Severity**: Low (labels stored in constants, positions match iteration)

### Flicker effect at dips
- **Spec says**: 1-2px lateral shake for 5-8 frames per dip (lines 39-43)
- **Implementation does**: Not visible in current implementation
- **Severity**: High (flicker/shake effect not implemented)

### Cost statistic callout
- **Spec says**: "$1.52T" in 36pt bold red-amber #E06040 at upper-right, subtitle "annual US tech debt cost (CISQ)" 18pt (lines 44-48)
- **Implementation does**: CostCallout component at lines 399-434, positioned at (1350, 120), "$1.52T" in 36pt, subtitle 16pt
- **Severity**: Low (implemented, subtitle font slightly smaller: 16pt vs 18pt)

### Cost callout timing
- **Spec says**: Frame 270-360 (9-12s) fade in (lines 94-97)
- **Implementation does**: Frame 200-260 (lines 536-543)
- **Severity**: Medium (earlier: starts frame 200 vs 270)

### Cost callout color
- **Spec says**: Value in red-amber #E06040 (line 45)
- **Implementation does**: Uses COLORS.DIP_RED (line 418)
- **Severity**: Low (needs constant verification for exact color)

### Red-tinted annotations
- **Spec says**: All dip annotations in red-tinted amber #E06040 with icons (lines 27-37)
- **Implementation does**: Uses COLORS.DIP_RED, no icons visible in Annotation component (lines 292-330)
- **Severity**: Medium (color likely correct, icons not implemented: arrow-down, revert, fork)

### PDD curve state during wobbles
- **Spec says**: PDD starting segment remains visible with faint blue glow (lines 50-52)
- **Implementation does**: Phase 1/4 PDD curve would be visible based on phase checks
- **Severity**: Low (persistence via phase system)

### Duration and hold
- **Spec says**: Frame 360-450 (12-15s) hold on damaged curve (lines 98-101)
- **Implementation does**: Phase 3 runs to accommodate wobble completion
- **Severity**: Low (implicit in phase system)

## Missing Elements

### Flicker/shake effect
- **Spec says**: Curve segments briefly flicker or shake laterally (1-2px) at each dip, 5-8 frames (lines 39-43)
- **Implementation does**: Not implemented
- **Severity**: High (visual effect entirely missing)

### Dip annotation icons
- **Spec says**: Small downward arrow icon for "new bug", circular "revert" icon for "regression", forking-paths icon for "merge conflict" (lines 28-36)
- **Implementation does**: Text-only annotations via Annotation component
- **Severity**: Medium (visual enhancement missing, reduces clarity)

### Thin red-tinted leader lines
- **Spec says**: Leader lines should be red-tinted to match dip annotations (lines 37-38)
- **Implementation does**: Leader lines use annotation color parameter, which is COLORS.DIP_RED (lines 311-317)
- **Severity**: Low (likely correct via color parameter)

Main issues: timing compression, missing flicker effect, missing dip annotation icons.
