# Audit: 02_patching_curve.md

## Spec Summary
The patching curve (amber) draws fully across the graph showing logarithmic growth with 12-15 dots representing individual patches. Includes two annotations ("one bug fixed", "local return only") and a dashed ceiling line. Duration ~20 seconds.

## Implementation Status
Implemented (Phase 2 of CompoundCurvesGraph.tsx)

## Deltas Found

### Curve mathematical function
- **Spec says**: `y = a * log(x + 1)` logarithmic form (line 25)
- **Implementation does**: `maxHeight * (Math.log(t * 5 + 1) / Math.log(6))` where maxHeight = GRAPH.HEIGHT * 0.7 (~560px) (lines 20-23)
- **Severity**: Low (correct logarithmic form with appropriate scaling)

### Animation duration differs from spec
- **Spec says**: Frame 0-450 (0-15s) for full curve draw, Frame 450-600 (15-20s) hold (lines 71-95)
- **Implementation does**: Frame 0-300 for curve progress 0.08→1.0 (lines 471-477)
- **Severity**: Medium (33% faster than spec - 300 frames vs 450 frames)

### Dot count matches spec range
- **Spec says**: 12-15 dots total (line 32)
- **Implementation does**: PATCH_DOT_COUNT constant, interpolates from 1 to PATCH_DOT_COUNT over frames 0-300 (lines 479-487)
- **Severity**: Low (needs constant verification)

### First annotation timing
- **Spec says**: Frame 90-150 (3-5s) "one bug fixed" near dot #3 (lines 76-80)
- **Implementation does**: Frame 60-100 opacity 0→1 (lines 488-494)
- **Severity**: Medium (earlier start: frame 60 vs 90)

### Second annotation timing
- **Spec says**: Frame 150-330 (5-11s) "local return only" near dot #6 (lines 82-85)
- **Implementation does**: Frame 120-160 opacity 0→1 (lines 495-501)
- **Severity**: High (significantly earlier: frames 120-160 vs 150-330)

### Ceiling line timing
- **Spec says**: Frame 330-450 (11-15s) dashed ceiling fades in (lines 86-89)
- **Implementation does**: Frame 220-300 opacity 0→0.4 (lines 502-508)
- **Severity**: Medium (earlier timing: 220-300 vs 330-450)

### Annotation positioning
- **Spec says**: Near dot #3 for "one bug fixed", near dot #6 for "local return only" (lines 76, 84)
- **Implementation does**: At position 3/(PATCH_DOT_COUNT+1) and 6/(PATCH_DOT_COUNT+1) (lines 726, 732)
- **Severity**: Low (correct relative positioning)

### Dot pop-in animation
- **Spec says**: `spring({ damping: 12, stiffness: 200 })` (line 207)
- **Implementation does**: Linear interpolate scale 0→1 over 10 frames per dot, staggered by 8 frames (lines 275-281)
- **Severity**: Medium (simplified to linear scale instead of spring physics)

### PDD curve during phase 2
- **Spec says**: PDD starting segment remains visible, slight blue glow, possibly pulse at end (lines 45-47, 94-95)
- **Implementation does**: Phase 1 curve segment persists via phase check at line 839-847
- **Severity**: Low (basic implementation, no explicit glow pulse mentioned in phase 2 code)

### Easing functions
- **Spec says**: Curve draw `easeOutQuad`, dot pop `spring`, annotations `easeOutCubic`, ceiling `easeOutQuad` (lines 206-210)
- **Implementation does**: Curve `Easing.out(Easing.quad)` (line 476), annotations no explicit easing (default), ceiling no explicit easing
- **Severity**: Low (curve easing matches, others default to linear)

## Missing Elements

### Study annotations on ceiling line
- **Spec says**: Dashed horizontal guide line at the flattening level (line 42)
- **Implementation does**: Dashed ceiling line at y=patchingBaseY(1) (lines 740-750)
- **Severity**: Low (implemented, positioned at t=1.0 height)

### Curve flattening visual emphasis
- **Spec says**: Vertical spacing between dots shrinks visibly as curve flattens (lines 83-84)
- **Implementation does**: Logarithmic function naturally produces this; dots positioned along curve (lines 710-719)
- **Severity**: Low (emerges from math, not explicitly coded)

All major elements present. Main deltas are timing compression (phase runs faster than spec) and simplified spring animation.
