# Audit: Section 6.4 -- The Triangle (Prompt, Tests, Grounding)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas Resolution and Background** -- PASS
   - Spec: 1920x1080, dark (#1a1a2e)
   - Implementation: `THREE_COMPONENTS_WIDTH = 1920`, `THREE_COMPONENTS_HEIGHT = 1080`, background `#1a1a2e`
   - Files: `37-ThreeComponents/constants.ts:8-9`, `37-ThreeComponents/ThreeComponents.tsx:302`

2. **Vertex Labels** -- PASS
   - Spec: PROMPT, TESTS, GROUNDING
   - Implementation: All three labels present and correct
   - Files: `37-ThreeComponents/ThreeComponents.tsx:232-234`

3. **Vertex Colors** -- PASS
   - Spec: PROMPT=#4A90D9 (blue), TESTS=#D9944A (amber), GROUNDING=#5AAA6E (green)
   - Implementation: `NOZZLE_BLUE: "#4A90D9"`, `WALLS_AMBER: "#D9944A"`, `GROUNDING_GREEN: "#5AAA6E"`
   - Files: `37-ThreeComponents/constants.ts:58-60`

4. **Vertex Node Visual Design** -- PASS
   - Spec: rounded rectangle (borderRadius 12), 2px solid border, background at 15% opacity of signature color, boxShadow glow (30px * intensity), minWidth 140, fontSize 20 bold, letterSpacing 2
   - Implementation matches all these values exactly
   - Files: `37-ThreeComponents/ThreeComponents.tsx:44-62`

5. **Staggered Vertex Appearance Timing** -- PASS
   - Spec: PROMPT at frame 0, TESTS 10 frames later, GROUNDING 10 frames later, 30-frame scale-up with easeOutBack(1.5) overshoot
   - Implementation: delays at 0, 10, 20 with 30-frame duration and `Easing.out(Easing.back(1.5))`
   - Files: `37-ThreeComponents/constants.ts:14-16`, `37-ThreeComponents/ThreeComponents.tsx:238-244`

6. **Edge Drawing Timing and Easing** -- PASS
   - Spec: Frames 60-120, easeOutCubic
   - Implementation: `EDGES_START: 60, EDGES_END: 120`, `Easing.out(Easing.cubic)`
   - Files: `37-ThreeComponents/constants.ts:20-21`, `37-ThreeComponents/ThreeComponents.tsx:247-252`

7. **Edge Visual Design** -- PASS
   - Spec: Gradient between connected vertex colors, 2px line width with glow, glow layer with blur
   - Implementation: SVG `linearGradient` with `gradientUnits="userSpaceOnUse"`, main line `strokeWidth={2}` at `opacity={0.8}`, glow layer `strokeWidth={6}` with `feGaussianBlur stdDeviation="4"` filter
   - Files: `37-ThreeComponents/ThreeComponents.tsx:91-138`, `314-316`

8. **Glow Intensification Timing** -- PASS
   - Spec: Frames 120-160, pulses from 0.6 to 1.0
   - Implementation: `GLOW_INTENSIFY_START: 120, GLOW_INTENSIFY_END: 160`, interpolation `[0.6, 1.0]`
   - Files: `37-ThreeComponents/constants.ts:24-25`, `37-ThreeComponents/ThreeComponents.tsx:255-260`

9. **Sub-label Fade Timing** -- PASS
   - Spec: Frames 130-170
   - Implementation: `SUBLABEL_START: 130, SUBLABEL_END: 170`
   - Files: `37-ThreeComponents/constants.ts:26-27`, `37-ThreeComponents/ThreeComponents.tsx:263-268`

10. **Sub-label Styling** -- PASS
    - Spec: italic, fontSize 15, color rgba(255,255,255,0.6), marginTop 10
    - Implementation matches all values
    - Files: `37-ThreeComponents/ThreeComponents.tsx:65-74`

11. **Center Code Block Visual** -- PASS
    - Spec: "Generated Code" label, monospace fontSize 13, gray rgba(160,160,160,0.6), background rgba(160,160,160,0.1), border 1px solid rgba(160,160,160,0.25), borderRadius 8, padding 12px 16px, NO GLOW, opacity max 0.5
    - Implementation matches all values. No boxShadow present (no glow). Opacity interpolates from 0 to 0.5.
    - Files: `37-ThreeComponents/ThreeComponents.tsx:382-406`

12. **Center Code Appearance Timing** -- PASS
    - Spec: Frames 180-220, opacity 0 to 0.5
    - Implementation: `CODE_START: 180, CODE_END: 220`, `[0, 0.5]`
    - Files: `37-ThreeComponents/constants.ts:30-31`, `37-ThreeComponents/ThreeComponents.tsx:271-276`

13. **Derivation Arrow Timing** -- PASS
    - Spec: Frames 200-240, opacity 0 to 0.3
    - Implementation: `ARROWS_START: 200, ARROWS_END: 240`, `[0, 0.3]`
    - Files: `37-ThreeComponents/constants.ts:32-33`, `37-ThreeComponents/ThreeComponents.tsx:279-284`

14. **Derivation Arrow Visual** -- PARTIAL
    - Spec: dashed, subtle, from edge midpoints toward centroid
    - Implementation: dashed (`strokeDasharray="6 4"`), gray (`rgba(160,160,160,0.4)`), 1.5px stroke, shortened 40%-80% of path. Arrows computed from edge midpoints toward centroid.
    - Files: `37-ThreeComponents/ThreeComponents.tsx:149-173`, `294-364`

15. **Hold Phase** -- PASS
    - Spec: Frames 240-300 hold complete diagram
    - Implementation: `HOLD_START: 240`, no further animation changes after this point (aside from formula at 600)
    - Files: `37-ThreeComponents/constants.ts:36`

16. **Integration in ClosingSection** -- PASS
    - ThreeComponents is Visual 3, starts at frame 391 (13.02s), aligns with narration "Prompts encode intent..."
    - Files: `S06-Closing/constants.ts:43-44`, `S06-Closing/ClosingSection.tsx:57-62`

### Issues Found

1. **Sub-label Text Does Not Match Spec -- MEDIUM**
   - Spec: "encodes intent", "preserves behavior", "maintains style"
   - Implementation: "Intent", "Constraints", "Style"
   - The spec explicitly defines full phrases as sub-labels and ties them to narration sync. The narration says "Prompts encode intent. Tests preserve behavior. Grounding maintains style." and the sub-labels are supposed to reinforce this. The single-word labels ("Constraints" for TESTS is also semantically different from "preserves behavior") lose the verb+noun structure that creates the intended mapping.
   - File: `37-ThreeComponents/ThreeComponents.tsx:232-234`

2. **No Per-Vertex Narration Pulse Sync -- MEDIUM**
   - Spec: "Each clause lands as its corresponding vertex glows brighter" with PROMPT pulsing on "Prompts encode intent", TESTS on "Tests preserve behavior", GROUNDING on "Grounding maintains style"
   - Implementation: All three vertices share a single `glowPulse` value that intensifies uniformly from frames 120-160. There is no per-vertex staggered pulse that activates as each narration clause is spoken. The sequential vertex-by-vertex glow effect described in the spec is entirely absent.
   - File: `37-ThreeComponents/ThreeComponents.tsx:255-260, 377`

3. **Edge Pulse Animation Missing -- MEDIUM**
   - Spec: "Subtle animated pulse along edges (energy flowing)"
   - Implementation: Edge glow intensity changes only during the intensification phase (frames 120-160) and is then static. There is no continuous animated pulse or energy-flowing effect traveling along the edge paths.
   - File: `37-ThreeComponents/ThreeComponents.tsx:91-138`

4. **Triangle Geometry Deviates from Spec -- MEDIUM**
   - Spec: centerX=960, centerY=480, radius=280, yielding PROMPT at (960, 200), TESTS at (717.5, 620), GROUNDING at (1202.5, 620)
   - Implementation: PROMPT at (960, 180), TESTS at (560, 700), GROUNDING at (1360, 700), CENTER_Y=440
   - The implementation triangle is substantially larger (effective horizontal span 800px vs 485px, vertical span 520px vs 420px) and positioned lower. The visual proportions are significantly different from the spec.
   - File: `37-ThreeComponents/constants.ts:44-53`

5. **Centroid Position Incorrect -- LOW-MEDIUM**
   - The geometric centroid of the implemented triangle is ((960+560+1360)/3, (180+700+700)/3) = (960, 526.7)
   - Implementation stores CENTROID as (960, 430), which is 97px above the true centroid
   - This places the "Generated Code" block closer to the PROMPT vertex rather than at the true center of the triangle, weakening the visual balance
   - File: `37-ThreeComponents/constants.ts:52`

6. **Missing Easing on Glow Intensification -- LOW**
   - Spec: "Glow intensification: easeOutQuad"
   - Implementation: `glowPulse` interpolation has no easing specified (defaults to linear)
   - File: `37-ThreeComponents/ThreeComponents.tsx:255-260`

7. **Missing Easing on Sub-label Fade -- LOW**
   - Spec: "Sub-labels: easeOutCubic"
   - Implementation: `subLabelOpacity` interpolation has no easing specified (defaults to linear)
   - File: `37-ThreeComponents/ThreeComponents.tsx:263-268`

8. **Missing Easing on Code Appearance -- LOW**
   - Spec: "Code appearance: easeOutQuad (gentle, understated)"
   - Implementation: `codeOpacity` interpolation has no easing specified (defaults to linear)
   - File: `37-ThreeComponents/ThreeComponents.tsx:271-276`

9. **Derivation Arrows Lack Arrowheads -- LOW**
   - Spec: "Three arrows from edges/vertices pointing inward toward center code"
   - Implementation: Dashed lines without arrowheads (no SVG marker-end). The word "arrows" implies directional indicators but the implementation renders plain dashed segments with no visual directionality.
   - File: `37-ThreeComponents/ThreeComponents.tsx:149-173`

10. **Missing extrapolateLeft Clamp on Vertex Scale -- LOW**
    - The `vertexScale` function does not specify `extrapolateLeft: "clamp"`. For TESTS (delay=10) at frame 0, and GROUNDING (delay=20) at frames 0-19, the interpolation extrapolates left from the input range, producing negative scale values. This could cause brief mirrored/inverted rendering of those vertices before their intended appearance.
    - File: `37-ThreeComponents/ThreeComponents.tsx:238-244`

11. **Integration Formula Not in Spec -- LOW (Additive)**
    - Implementation includes an IntegrationFormula component (frames 600-660) showing "Prompt + Tests + Grounding / Intent + Constraints + Style / = Complete Specification". This is not part of the Section 6.4 spec.
    - In the ClosingSection context, ThreeComponents runs for ~181 frames (6 seconds), so the formula at frame 600 never appears. This is effectively dead code in the closing section context but would appear in the standalone composition.
    - File: `37-ThreeComponents/ThreeComponents.tsx:176-224, 409`, `37-ThreeComponents/constants.ts:39-40`

12. **Duration Mismatch -- LOW**
    - Spec: ~10 seconds (300 frames)
    - Standalone composition: 25 seconds (750 frames)
    - In ClosingSection: ~6 seconds (frames 391-572 = 181 relative frames)
    - The standalone duration is 2.5x the spec. In closing context, only ~6 seconds are allocated, meaning the animation only reaches partway through the hold phase.
    - File: `37-ThreeComponents/constants.ts:5`

### Notes

- The ThreeComponents composition is reused across Section 3 (Part3MoldThreeParts, Visual 18) and Section 6 (ClosingSection, Visual 3). The sub-label simplification ("Intent"/"Constraints"/"Style" vs full phrases) may be a compromise for dual-context reuse, but it conflicts with the Section 6.4 spec's explicit text and narration sync requirements.
- The most impactful issues are #1 (sub-label text), #2 (narration pulse sync), and #3 (edge pulse). These three together mean the narration-synced visual reinforcement described in the spec is not implemented. The spec envisions each vertex pulsing individually as its narration clause is spoken, with sub-labels appearing in sync. The implementation instead applies uniform glow to all vertices simultaneously.
- All color constants match the spec exactly.
- The vertex node component, edge component, and center code block styling are faithfully implemented with the spec's CSS values.
- The animation phase ordering (vertices -> edges -> glow -> sub-labels -> code -> arrows -> hold) follows the spec sequence correctly.
- The vertex appearance easing (easeOutBack with overshoot) and edge drawing easing (easeOutCubic) match the spec. The three missing easings (#6-8) are on secondary animations.

## Resolution Status: UNRESOLVED
