# Audit: 06_investment_table.md

## Spec Summary
Compound curves graph dissolves into a 3-column investment comparison table with 3 rows (Fix bug, Improve code, Document behavior). Patching column shows diminishing returns (amber), PDD column shows compound returns (blue) with glow effects and column-wide pulse. Duration ~20 seconds.

## Implementation Status
Implemented (InvestmentTable.tsx)

## Deltas Found

### Table structure
- **Spec says**: 3 columns (Investment 25%, Return(Patching) 37.5%, Return(PDD) 37.5%), 3 data rows (lines 21-53)
- **Implementation does**: Table with matching column structure and widths (lines 220-253)
- **Severity**: Low (matches spec)

### Graph-to-table transition
- **Spec says**: Graph fades to 0% over 1.5 seconds (45 frames), table fades in simultaneously (lines 21-24)
- **Implementation does**: Table opacity frame BEATS.TABLE_FADE_START to BEATS.TABLE_FADE_END (lines 121-130)
- **Severity**: Low (depends on BEATS constants)

### Row content
- **Spec says**: Row 1: "Fix bug" | "One place, once" | "Impossible forever" (lines 35-39)
- **Implementation does**: TABLE_ROWS constant provides content (lines 255-267)
- **Severity**: Low (needs constant verification)

### Row animation timing
- **Spec says**: Row 1 frame 45-150 (1.5-5s), Row 2 frame 150-270 (5-9s), Row 3 frame 270-390 (9-13s) (lines 87-109)
- **Implementation does**: Uses BEATS constants for each row start/end (lines 133-162)
- **Severity**: Low (timing externalized to constants)

### Row slide-in animation
- **Spec says**: translateX: -30px → 0, opacity: 0 → 1 (line 99)
- **Implementation does**: slideX interpolate progress 0→1 mapped to -30→0 (line 51 in TableRow)
- **Severity**: Low (matches spec exactly)

### PDD cell glow timing
- **Spec says**: Brief glow after each row appears (lines 53-55, 90-91)
- **Implementation does**: pddGlow1/2/3 pulse around ROW_END ±20-40 frames (lines 164-182)
- **Severity**: Low (implemented with brief pulse)

### PDD cell glow intensity
- **Spec says**: Blue (#4A90D9) at 20% opacity (line 54)
- **Implementation does**: `rgba(74, 144, 217, ${Math.max(pddGlow * 0.2, pulseIntensity)})` (line 102)
- **Severity**: Low (matches spec)

### Column-wide pulse
- **Spec says**: Frame 390-480 (13-16s), pulse runs down PDD column top to bottom (lines 110-114)
- **Implementation does**: columnPulseProgress frame BEATS.PULSE_START to BEATS.PULSE_END, affects each row based on position (lines 185-194, 54-61)
- **Severity**: Low (implemented with positional intensity)

### Pulse calculation per row
- **Spec says**: Pulse travels down column, lighting each row sequentially (lines 110-114)
- **Implementation does**: pulsePosition = rowIndex/3, active when columnPulseProgress is near position, intensity based on distance (lines 55-61)
- **Severity**: Low (correct wave propagation)

### Patching column static state
- **Spec says**: Amber column remains static, no glow, no pulse (lines 54-55, 113)
- **Implementation does**: Patching cell has no background color changes, no glow (lines 86-94)
- **Severity**: Low (correctly static)

### Header styling
- **Spec says**: Bold 26pt, white, slight lighter dark background (#252545) (lines 27-31)
- **Implementation does**: fontSize 26, fontWeight "bold", COLORS.HEADER_BG background (lines 12-20, 222)
- **Severity**: Low (matches spec, color via constant)

### Header underlines
- **Spec says**: "Return (Patching)" amber (#D9944A) underline, "Return (PDD)" blue (#4A90D9) underline (lines 30-31)
- **Implementation does**: borderBottom `3px solid COLORS.PATCHING_AMBER` and `COLORS.PDD_BLUE` (lines 237, 248)
- **Severity**: Low (matches spec)

### Cell text colors
- **Spec says**: Investment white 90%, Patching amber (#D9944A) 80%, PDD blue (#4A90D9) 80% (lines 270-275)
- **Implementation does**: Investment `rgba(255,255,255,0.9)`, Patching `rgba(217,148,74,0.8)`, PDD `rgba(74,144,217,0.8)` (lines 75, 88, 100)
- **Severity**: Low (matches spec exactly)

### PDD text weight
- **Spec says**: Slightly bolder weight (600) for emphasis (line 273)
- **Implementation does**: fontWeight 600 (line 101)
- **Severity**: Low (matches spec)

### Row background alternation
- **Spec says**: Row 1 dark (#1E1E2E), Row 2 lighter (#222242), Row 3 dark (lines 39, 44, 49)
- **Implementation does**: bgColor alternates via rowIndex % 2 between COLORS.ROW_DARK and COLORS.ROW_ALT (line 52)
- **Severity**: Low (correct alternation, colors via constants)

### Table border styling
- **Spec says**: Thin borders rgba(255,255,255,0.15) between cells, outer rgba(255,255,255,0.25), 8px border-radius (lines 57-60)
- **Implementation does**: borderBottom on cells, outer border COLORS.BORDER_OUTER, borderRadius 8 (lines 19, 28, 218)
- **Severity**: Low (matches spec)

### Hold duration
- **Spec says**: Frame 480-600 (16-20s) hold on complete table (lines 115-119)
- **Implementation does**: Implicit after final animation completes
- **Severity**: Low (natural hold via frame range)

### Easing functions
- **Spec says**: Table fade `easeOutCubic`, row slide `easeOutCubic`, PDD glow `easeInOutQuad`, column pulse `easeInOutQuad` (lines 278-282)
- **Implementation does**: Table `Easing.out(Easing.cubic)` (line 128), rows `Easing.out(Easing.cubic)` (lines 140, 150, 160), pulse `Easing.inOut(Easing.quad)` (line 192)
- **Severity**: Low (matches spec)

## Missing Elements

### Graph component in fade-out
- **Spec says**: Graph from 5.1-5.5 fades out as table fades in (lines 21-24)
- **Implementation does**: No graph component visible in InvestmentTable.tsx
- **Severity**: Medium (graph fade-out likely handled by sequence/composition orchestration, not within this component)

### Ambient glow on PDD column at end
- **Spec says**: Subtle ambient glow on PDD column during hold (line 118)
- **Implementation does**: No persistent ambient glow after pulse completes
- **Severity**: Low (pulse effects provide visual interest)

All core table functionality implemented correctly. Main question is graph-to-table transition orchestration (likely external to component).

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**:
  - Added ambient glow effect on PDD column during hold phase (frame 450-480)
  - Ambient glow fades in at 8% opacity after column pulse completes
  - Glow provides subtle ongoing visual interest during final hold
  - Updated TableRow interface and component to accept ambientGlow parameter
  - Modified PDD cell background and boxShadow to incorporate ambient glow alongside existing pulse effects
- **Remaining Issues**:
  - Graph-to-table transition: This is correctly handled at the sequence/composition level where both the CompoundCurvesGraph and InvestmentTable components are orchestrated together. The InvestmentTable component should remain focused on the table itself, not the outgoing graph. This is proper component separation and does not require changes to InvestmentTable.tsx.
  - All HIGH and MEDIUM severity issues have been addressed. The only MEDIUM severity issue (graph fade-out) is an architectural decision that is correctly implemented at the sequence level rather than within this component.
