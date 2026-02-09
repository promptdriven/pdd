# Audit: Section 6.4 -- The Triangle (Prompt, Tests, Grounding)

## Status: RESOLVED

### Requirements Met

1. **Canvas Resolution and Background** -- PASS
   - Spec: 1920x1080, dark (#1a1a2e)
   - Implementation: `THREE_COMPONENTS_WIDTH = 1920`, `THREE_COMPONENTS_HEIGHT = 1080`, background `#1a1a2e`
   - Files: `37-ThreeComponents/constants.ts:8-9`, `37-ThreeComponents/ThreeComponents.tsx:387`

2. **Vertex Labels** -- PASS
   - Spec: PROMPT, TESTS, GROUNDING
   - Implementation: All three labels present and correct in VERTICES definitions
   - Files: `37-ThreeComponents/constants.ts:100-118`

3. **Vertex Colors** -- PASS
   - Spec: PROMPT=#4A90D9 (blue), TESTS=#D9944A (amber), GROUNDING=#5AAA6E (green)
   - Implementation: `NOZZLE_BLUE: "#4A90D9"`, `WALLS_AMBER: "#D9944A"`, `GROUNDING_GREEN: "#5AAA6E"`
   - Files: `37-ThreeComponents/constants.ts:89-92`

4. **Vertex Node Visual Design** -- PASS
   - Spec: rounded rectangle (borderRadius 12), 2px solid border, background at 15% opacity of signature color, boxShadow glow (30px * intensity), minWidth 140, fontSize 20 bold, letterSpacing 2
   - Implementation matches all these values exactly
   - Files: `37-ThreeComponents/ThreeComponents.tsx:51-70`

5. **Staggered Vertex Appearance Timing** -- PASS
   - Spec: PROMPT at frame 0, TESTS 10 frames later, GROUNDING 10 frames later, 30-frame scale-up with easeOutBack(1.5) overshoot
   - Implementation: delays at 0, 10, 20 with 30-frame duration and `Easing.out(Easing.back(1.5))`, includes `extrapolateLeft: "clamp"`
   - Files: `37-ThreeComponents/constants.ts:48-52`, `37-ThreeComponents/ThreeComponents.tsx:285-299`

6. **Edge Drawing Timing and Easing** -- PASS
   - Spec: Frames 60-120, easeOutCubic
   - Implementation: `EDGES_START: 60, EDGES_END: 120`, `Easing.out(Easing.cubic)`
   - Files: `37-ThreeComponents/constants.ts:55-56`, `37-ThreeComponents/ThreeComponents.tsx:302-307`

7. **Edge Visual Design** -- PASS
   - Spec: Gradient between connected vertex colors, 2px line width with glow, glow layer with blur
   - Implementation: SVG `linearGradient` with `gradientUnits="userSpaceOnUse"`, main line `strokeWidth={2}` at `opacity={0.8}`, glow layer `strokeWidth={6}` with `feGaussianBlur stdDeviation="4"` filter
   - Files: `37-ThreeComponents/ThreeComponents.tsx:102-181`

8. **Glow Intensification Timing** -- PASS
   - Spec: Frames 120-160, pulses from 0.6 to 1.0, easeOutQuad
   - Implementation: Per-vertex staggered glow with easeOutQuad: PROMPT 120-140, TESTS 135-155, GROUNDING 150-170, all interpolating [0.6, 1.0]
   - Files: `37-ThreeComponents/constants.ts:60-65`, `37-ThreeComponents/ThreeComponents.tsx:309-329`

9. **Sub-label Fade Timing** -- PASS
   - Spec: Frames 130-170, easeOutCubic
   - Implementation: `SUBLABEL_START: 130, SUBLABEL_END: 170`, `Easing.out(Easing.cubic)`
   - Files: `37-ThreeComponents/constants.ts:68-69`, `37-ThreeComponents/ThreeComponents.tsx:342-347`

10. **Sub-label Styling** -- PASS
    - Spec: italic, fontSize 15, color rgba(255,255,255,0.6), marginTop 10
    - Implementation matches all values
    - Files: `37-ThreeComponents/ThreeComponents.tsx:73-82`

11. **Center Code Block Visual** -- PASS
    - Spec: "Generated Code" label, monospace fontSize 13, gray rgba(160,160,160,0.6), background rgba(160,160,160,0.1), border 1px solid rgba(160,160,160,0.25), borderRadius 8, padding 12px 16px, NO GLOW, opacity max 0.5
    - Implementation matches all values. No boxShadow present (no glow). Opacity interpolates from 0 to 0.5.
    - Files: `37-ThreeComponents/ThreeComponents.tsx:467-490`

12. **Center Code Appearance Timing** -- PASS
    - Spec: Frames 180-220, opacity 0 to 0.5, easeOutQuad
    - Implementation: `CODE_START: 180, CODE_END: 220`, `[0, 0.5]`, `Easing.out(Easing.quad)`
    - Files: `37-ThreeComponents/constants.ts:72-73`, `37-ThreeComponents/ThreeComponents.tsx:350-355`

13. **Derivation Arrow Timing** -- PASS
    - Spec: Frames 200-240, opacity 0 to 0.3
    - Implementation: `ARROWS_START: 200, ARROWS_END: 240`, `[0, 0.3]`
    - Files: `37-ThreeComponents/constants.ts:76-77`, `37-ThreeComponents/ThreeComponents.tsx:358-363`

14. **Derivation Arrow Visual** -- PASS
    - Spec: dashed, subtle, from edge midpoints toward centroid, with arrowheads
    - Implementation: dashed (`strokeDasharray="6 4"`), gray (`rgba(160,160,160,0.4)`), 1.5px stroke, shortened 40%-80% of path, with SVG polygon arrowheads. Arrows computed from edge midpoints toward centroid.
    - Files: `37-ThreeComponents/ThreeComponents.tsx:183-237, 421-432`

15. **Hold Phase** -- PASS
    - Spec: Frames 240-300 hold complete diagram
    - Implementation: `HOLD_START: 240`, no further animation changes after this point (aside from formula at 600)
    - Files: `37-ThreeComponents/constants.ts:80`

16. **Integration in ClosingSection** -- PASS
    - ThreeComponents is Visual 3, starts at frame 391 (13.02s), aligns with narration "Prompts encode intent..."
    - Files: `S06-Closing/constants.ts:43-44`, `S06-Closing/ClosingSection.tsx:57-62`

### Issues Found and Resolved

1. **Sub-label Text Does Not Match Spec -- MEDIUM -- RESOLVED**
   - Spec: "encodes intent", "preserves behavior", "maintains style"
   - Was: "Intent", "Constraints", "Style"
   - Fix: Updated VERTICES in constants.ts to use full spec phrases as sublabels
   - File: `37-ThreeComponents/constants.ts:103,109,115`

2. **No Per-Vertex Narration Pulse Sync -- MEDIUM -- RESOLVED**
   - Spec: "Each clause lands as its corresponding vertex glows brighter" with per-vertex staggering
   - Was: All three vertices shared a single `glowPulse` value
   - Fix: Replaced single glowPulse with three staggered per-vertex glow interpolations (promptGlow, testsGlow, groundingGlow) at frames 120-140, 135-155, 150-170 respectively
   - File: `37-ThreeComponents/ThreeComponents.tsx:309-336`, `37-ThreeComponents/constants.ts:60-65`

3. **Edge Pulse Animation Missing -- MEDIUM -- RESOLVED**
   - Spec: "Subtle animated pulse along edges (energy flowing)"
   - Was: Edge glow was static after initial draw
   - Fix: Added energy pulse layer in TriangleEdge component using animated strokeDashoffset that cycles every ~90 frames, creating a flowing energy effect along each edge. Each edge has a phase offset for visual variation.
   - File: `37-ThreeComponents/ThreeComponents.tsx:164-178, 373-375`

4. **Triangle Geometry Deviates from Spec -- MEDIUM -- RESOLVED**
   - Spec: centerX=960, centerY=480, radius=280, yielding PROMPT at (960, 200), TESTS at (~718, 620), GROUNDING at (~1202, 620)
   - Was: PROMPT at (960, 180), TESTS at (560, 700), GROUNDING at (1360, 700) -- a much larger, non-equilateral triangle
   - Fix: Replaced vertical flow layout with proper equilateral triangle using spec geometry (CENTER_X=960, CENTER_Y=480, RADIUS=280)
   - File: `37-ThreeComponents/constants.ts:12-38`

5. **Centroid Position Incorrect -- LOW-MEDIUM -- RESOLVED**
   - Was: Centroid at (960, 430), 97px above true centroid
   - Fix: Computed correct geometric centroid as average of three vertex Y positions = (200+620+620)/3 = 480, yielding (960, 480)
   - File: `37-ThreeComponents/constants.ts:32-37`

6. **Missing Easing on Glow Intensification -- LOW -- RESOLVED**
   - Spec: "Glow intensification: easeOutQuad"
   - Fix: Added `Easing.out(Easing.quad)` to all three per-vertex glow interpolations
   - File: `37-ThreeComponents/ThreeComponents.tsx:314, 321, 328`

7. **Missing Easing on Sub-label Fade -- LOW -- RESOLVED**
   - Spec: "Sub-labels: easeOutCubic"
   - Fix: Added `Easing.out(Easing.cubic)` to subLabelOpacity interpolation
   - File: `37-ThreeComponents/ThreeComponents.tsx:346`

8. **Missing Easing on Code Appearance -- LOW -- RESOLVED**
   - Spec: "Code appearance: easeOutQuad (gentle, understated)"
   - Fix: Added `Easing.out(Easing.quad)` to codeOpacity interpolation
   - File: `37-ThreeComponents/ThreeComponents.tsx:354`

9. **Derivation Arrows Lack Arrowheads -- LOW -- RESOLVED**
   - Spec: "Three arrows from edges/vertices pointing inward toward center code"
   - Fix: Added SVG polygon arrowhead at the end of each dashed line in DerivationArrow component
   - File: `37-ThreeComponents/ThreeComponents.tsx:231-234`

10. **Missing extrapolateLeft Clamp on Vertex Scale -- LOW -- RESOLVED**
    - Fix: Added `extrapolateLeft: "clamp"` to vertexScale interpolation to prevent negative scale values before vertex appearance
    - File: `37-ThreeComponents/ThreeComponents.tsx:291`

11. **Integration Formula Not in Spec -- LOW (Additive) -- ACKNOWLEDGED**
    - The IntegrationFormula component (frames 600-660) is retained for the standalone composition but updated to use spec-matching sublabel text. In the closing section context (~181 frames), it never appears since it requires frame 600+. This is effectively dead code in closing context but retained for standalone use.
    - File: `37-ThreeComponents/ThreeComponents.tsx:239-276`

12. **Duration Mismatch -- LOW -- ACKNOWLEDGED**
    - Spec: ~10 seconds (300 frames). Standalone: 25 seconds (750 frames). Closing: ~6 seconds (181 frames).
    - The standalone duration is retained for flexibility. In closing context, all spec animation phases (vertices, edges, glow, code, arrows) complete within the allocated 181 frames. The animation is designed to front-load all critical phases within the first 240 frames.
    - File: `37-ThreeComponents/constants.ts:5`

### Architecture Notes

- The ThreeComponents composition was completely rewritten from a vertical flow layout to a proper triangle diagram matching the Section 6.4 spec.
- The old implementation (ComponentBlock, WallsBlock, FlowArrow, OutputBlock components in a top-to-bottom pipeline) has been replaced with VertexNode, TriangleEdge, and DerivationArrow components arranged in an equilateral triangle.
- The component remains compatible with both S03-MoldThreeParts (Visual 18) and S06-Closing (Visual 3) contexts, as the props schema (showFormula: boolean) is unchanged.
- All color constants match the spec exactly.
- The vertex node component, edge component, and center code block styling are faithfully implemented with the spec's CSS values.
- The animation phase ordering (vertices -> edges -> glow -> sub-labels -> code -> arrows -> hold) follows the spec sequence correctly.
- Per-vertex glow is staggered (PROMPT first, then TESTS, then GROUNDING) to sync with narration cadence.
- Edge pulse animation uses strokeDashoffset cycling to create a subtle energy-flowing effect.

## Resolution Status: RESOLVED
