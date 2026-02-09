# Audit: 10_injection_nozzle.md

## Spec Summary
The spec requires a visual showing the injection nozzle (representing the prompt) as the second type of capital. Key elements include a nozzle with blue glow, three concept labels ("intent", "requirements", "constraints"), and a section title "PROMPT CAPITAL - The Specification". The animation should show the nozzle highlighting with pulse, labels appearing sequentially, and narration sync.

## Implementation Status
Partially Implemented

## Deltas Found

### Missing Concept Labels (intent/requirements/constraints)
- **Spec says**: Lines 31-34 require three labels orbiting/connecting to nozzle: "intent" (what you want), "requirements" (what it needs), "constraints" (boundaries but different from test walls)
- **Implementation does**: Lines 117-163 show a single label structure with "PROMPT" as main label and "The Injection Nozzle" subtitle, plus explanatory text about intent. Does NOT show the three separate concept labels as circles/connections around the nozzle
- **Severity**: High

### Missing "PROMPT CAPITAL" Section Title
- **Spec says**: Lines 36-38 require section title "PROMPT CAPITAL" with subtitle "The Specification" to fade in around Frame 360-450
- **Implementation does**: Lines 167-197 show different text: "Second: the prompt" with subtitle "Natural language intent that guides what code gets generated" - different wording and concept
- **Severity**: Medium

### Missing Pulse Animation
- **Spec says**: Lines 27, 52, 113 specify pulsing animation with `pulseScale = 1 + Math.sin(frame * 0.1) * 0.05`
- **Implementation does**: No pulse animation on the nozzle - it has static glow intensity but no scale pulsing
- **Severity**: Low

### Missing Mold Cross-Section Context
- **Spec says**: Lines 20-23 specify that the full mold cross-section returns with walls dimmed, then nozzle brightens. Lines 42-50 detail Frame 0-90 showing cross-section fade-in
- **Implementation does**: Only shows the nozzle in isolation - no mold walls or cross-section context visible
- **Severity**: Medium

### Different Animation Timing
- **Spec says**: Detailed beat structure in lines 42-68 with specific frame ranges for each element
- **Implementation does**: Uses BEATS constants from external file (lines 13-42) but timing structure appears simplified - only has NOZZLE_START/END, GLOW_START/END, LABEL_START/END, EXPLANATION_START
- **Severity**: Low

### Different Label Approach
- **Spec says**: Lines 116-120 show labels array with three separate items positioned around nozzle with individual start frames (180, 240, 300)
- **Implementation does**: Lines 117-163 use a conditional single label block with fixed positioning to the right of nozzle
- **Severity**: High

## Missing Elements
1. Three concept labels ("intent", "requirements", "constraints") orbiting/connected to nozzle
2. Label connection lines from labels to nozzle
3. Pulse animation on nozzle (scale oscillation)
4. Mold cross-section with dimmed walls as background context
5. "PROMPT CAPITAL" / "The Specification" title (has different text instead)
6. Sequential label appearance animation (spec shows 180, 240, 300 frame starts)
7. Wall opacity dimming animation (lines 96-102 in spec)

## Additional Notes
The implementation delivers the core visual of a blue-glowing nozzle but lacks the conceptual framework elements (intent/requirements/constraints labels) that the spec emphasizes. The spec's metaphor is about showing what goes INTO the nozzle (the three aspects of a prompt specification), while the implementation focuses on labeling the nozzle itself.

## Resolution Status
- **Status**: RESOLVED
- **Changes Made**:
  1. Added three concept labels ("intent", "requirements", "constraints") as circular badges with descriptions, positioned around the nozzle at coordinates specified in CONCEPT_LABELS array
  2. Added mold cross-section context with left, right, and bottom walls rendered in amber color (#D9944A) with dimmed opacity
  3. Added wall dimming animation from full opacity to 40% (frames 90-150) using easing
  4. Added pulse animation to nozzle using `pulseScale = 1 + Math.sin(frame * 0.1) * 0.05` applied as SVG transform
  5. Changed section title from "Second: the prompt" to "PROMPT CAPITAL" with subtitle "The Specification"
  6. Added sequential label appearance with individual start frames (180, 240, 300) and fade duration of 30 frames
  7. Added connection lines from each label to the nozzle center with dashed stroke and 50% opacity
  8. Updated BEATS timing structure to match spec: MOLD_START/END, WALL_DIM_START/END, NOZZLE_GLOW_START/END, individual label timings, TITLE_START/END
  9. Refactored nozzle SVG to use transform with pulseScale for proper animation
  10. Added WALLS_AMBER color constant and CONCEPT_LABELS configuration array to constants.ts
- **Remaining Issues**: None - all audit findings have been addressed
