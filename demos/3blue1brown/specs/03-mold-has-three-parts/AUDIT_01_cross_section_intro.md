# Audit: 01_cross_section_intro.md

## Spec Summary
Introduces the mold cross-section with three distinct regions (Walls, Nozzle, Material) highlighting sequentially over 15 seconds. Each region pulses with its color when introduced, with labels fading in for "Walls", "Nozzle", and "Material".

## Implementation Status
Implemented

## Deltas Found

### Label Names Mismatch
- **Spec says**: Labels should be "Walls", "Nozzle", "Material"
- **Implementation does**: Labels are "TESTS (Constraints)", "PROMPT (Intent)", "GROUNDING (Style)" (lines 159-199)
- **Severity**: High - This is a fundamental naming difference that changes the metaphor presentation

### Duration Mismatch
- **Spec says**: Duration of ~15 seconds (450 frames at 30fps)
- **Implementation does**: Duration is 10 seconds (300 frames) per constants.ts lines 5-7
- **Severity**: High - 33% shorter than specified

### Timing Sequence Different
- **Spec says**:
  - Frame 0-90: Mold fades in
  - Frame 90-150: Walls highlight
  - Frame 150-210: Nozzle highlights
  - Frame 210-270: Material highlights
  - Frame 270-450: All three visible
- **Implementation does**:
  - Frame 0-60: Outline fades in
  - Frame 60-120: Walls glow
  - Frame 120-180: Nozzle glows
  - Frame 180-240: Material glows
  - Frame 240-300: Labels appear
- **Severity**: Medium - Timeline is compressed and sequencing differs

### Missing Pulse Animation
- **Spec says**: "Brief pulse animation" for each region as it highlights
- **Implementation does**: Simple glow fade-in with drop-shadow, no visible pulse effect
- **Severity**: Low - Visual polish detail

### Title Text Addition
- **Spec says**: No title mentioned in spec
- **Implementation does**: Adds "The Mold Has Three Parts" title at bottom (lines 204-218)
- **Severity**: Low - Addition, not contradiction

### Label Presentation Style
- **Spec says**: Simple labels like "Walls", "Nozzle", "Material"
- **Implementation does**: Two-line labels with main term and parenthetical subtitle
- **Severity**: Medium - More verbose than specified

## Missing Elements
- No grid lines on mold for "technical feel" as mentioned in spec line 24
- No explicit easing for pulse animation (spec calls for `easeInOutSine` for pulse)
- Labels should pulse with regions, but implementation shows labels appearing after all regions are lit
