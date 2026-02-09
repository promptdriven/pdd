# Audit: 04_pdd_curve.md

## Spec Summary
PDD curve (blue) activates and draws forward from dormant segment to ~50% of X-axis with exponential (convex) shape. Each test dot sends forward radial lines showing compound effect. Includes annotation "constrains all future generations". Duration ~10 seconds.

## Implementation Status
Implemented (Phase 4 of CompoundCurvesGraph.tsx)

## Deltas Found

### Curve mathematical function
- **Spec says**: Exponential `y = a * (e^(bx) - 1)`, convex upward (line 24)
- **Implementation does**: `maxHeight * ((Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1))` where maxHeight = GRAPH.HEIGHT * 0.88 (~700px) (lines 38-41)
- **Severity**: Low (correct exponential form with normalization)

### Activation pulse
- **Spec says**: Frame 0-30 (0-1s) dormant segment brightens, pulse of light runs along it, glow intensifies (lines 73-77)
- **Implementation does**: Activation interpolates frame 0-30 from 0.5→1.0 opacity (lines 546-552)
- **Severity**: Medium (simple opacity change, no "pulse running along" animation)

### Curve draw timing
- **Spec says**: Frame 30-240 (1-8s) curve extends from ~8% to ~50% of X-axis (lines 78-84, 92-98)
- **Implementation does**: Frame 30-240 progress from 0.08→0.5 (lines 553-560)
- **Severity**: Low (matches spec exactly)

### Test dot count
- **Spec says**: 6-8 dots visible by end (lines 29-31, 99)
- **Implementation does**: Interpolates frame 30-240 from 0→8 dots (lines 561-569)
- **Severity**: Low (8 dots, within spec range)

### Forward radial lines
- **Spec says**: 2-3 faint lines project forward from each dot to right edge, light blue #6AB0E9 at 30% opacity (lines 34-39)
- **Implementation does**: ForwardRadials component renders 3 lines (offsets [0, -15, 15]) in COLORS.PDD_GLOW at opacity * 0.3 (lines 333-359, used at 798-811)
- **Severity**: Low (3 lines, color and opacity via constants)

### Forward radial line accumulation
- **Spec says**: Each new dot's radial lines overlay with previous ones, creating accumulating density (lines 38-39)
- **Implementation does**: Loops through all visible dots rendering ForwardRadials for each (lines 799-810)
- **Severity**: Low (correct accumulation via loop)

### Annotation text and timing
- **Spec says**: "constrains all future generations" near dot #3, frame 120-180 (4-6s) (lines 85-88)
- **Implementation does**: Frame 120-160, text matches, positioned at dot 3/(PDD_DOT_COUNT+1) (lines 570-576, 824-834)
- **Severity**: Low (20 frames earlier end: 160 vs 180)

### Annotation emphasis
- **Spec says**: Forward radial lines from this dot pulse brighter briefly, leader line draws (lines 86-88)
- **Implementation does**: Standard Annotation component, no special pulse for this dot
- **Severity**: Medium (radial pulse emphasis not implemented)

### Patching curve dimming
- **Spec says**: Wobbly patching curve from 5.3 remains visible at reduced opacity (60%) (lines 47-49)
- **Implementation does**: patchingDimOpacity interpolates frame 0-30 from 1→0.6 (lines 577-583, applied at line 699)
- **Severity**: Low (matches spec exactly)

### Blue glow on PDD curve
- **Spec says**: Subtle blue glow (feGaussianBlur, 4px) (lines 26-27)
- **Implementation does**: glowId="pddGlow" with glowStd=4 in phase 4 (lines 210-244, applied at 792)
- **Severity**: Low (matches spec)

### Easing functions
- **Spec says**: Activation pulse `easeOutQuad`, curve draw `easeInQuad` (accelerating), dots `spring`, radials `easeOutCubic` (lines 204-209)
- **Implementation does**: Curve `Easing.in(Easing.quad)` (line 558), activation and other elements use defaults
- **Severity**: Low (curve easing matches, others simplified)

### Convex shape visibility
- **Spec says**: Curve clearly convex (slope increasing) contrasting with patching concave (lines 8-9, 96-97)
- **Implementation does**: Exponential function produces convex shape naturally
- **Severity**: Low (mathematical property, visually correct)

## Missing Elements

### Activation pulse animation detail
- **Spec says**: "A pulse of light runs along the existing segment" (lines 75-76)
- **Implementation does**: Simple opacity increase, no traveling pulse
- **Severity**: Medium (less dramatic activation than spec suggests)

### Radial line brightness pulse for annotation
- **Spec says**: Forward radial lines from dot #3 pulse brighter when annotation appears (lines 86-87)
- **Implementation does**: No special treatment for dot #3 radials
- **Severity**: Low (subtle enhancement missing)

### Hold timing
- **Spec says**: Frame 240-300 (8-10s) hold with all elements visible (lines 94-99)
- **Implementation does**: Implicit via phase timing
- **Severity**: Low (phase system handles this)

Overall implementation is solid. Main gaps: simplified activation (no traveling pulse), missing radial emphasis for annotated dot.
