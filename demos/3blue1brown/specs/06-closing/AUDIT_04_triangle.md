# Audit: Section 6.4 -- The Triangle (Prompt, Tests, Grounding)

## Status: ISSUES FOUND

### Requirements Met

1. **Canvas and Background**: Implementation uses 1920x1080 resolution with dark background `#1a1a2e`. Matches spec exactly. (`constants.ts:8-9`, `ThreeComponents.tsx:302`)

2. **Triangle Vertex Labels**: Three vertices labeled PROMPT, TESTS, GROUNDING. All present with correct label text. (`ThreeComponents.tsx:232-234`)

3. **Vertex Colors**: PROMPT uses `#4A90D9` (blue), TESTS uses `#D9944A` (amber), GROUNDING uses `#5AAA6E` (green). All match spec. (`constants.ts:58-60`)

4. **Vertex Node Visual Design**: Rounded rectangles (borderRadius 12) with label and glow. Background at 15% opacity of signature color, 2px solid border, boxShadow glow, minWidth 140, fontSize 20 bold with letterSpacing 2. Matches spec code structure exactly. (`ThreeComponents.tsx:44-62`)

5. **Staggered Vertex Appearance**: PROMPT at frame 0, TESTS at frame 10, GROUNDING at frame 20 -- each with 30-frame scale-up from 0 to 1. Uses `Easing.out(Easing.back(1.5))` overshoot. All match spec. (`constants.ts:14-16`, `ThreeComponents.tsx:238-244`)

6. **Edge Drawing**: Edges draw from frame 60 to 120 with `easeOutCubic`. Gradient colors between connected vertex colors using SVG `linearGradient`. Glow layer at strokeWidth 6 with blur filter, main line at strokeWidth 2 with opacity 0.8. Matches spec. (`constants.ts:20-21`, `ThreeComponents.tsx:91-138`, `246-252`)

7. **Glow Intensification**: Pulses from 0.6 to 1.0 over frames 120-160. Matches spec. (`constants.ts:24-25`, `ThreeComponents.tsx:255-260`)

8. **Sub-label Fade-in Timing**: Sub-labels fade in over frames 130-170. Matches spec range. (`constants.ts:26-27`, `ThreeComponents.tsx:263-268`)

9. **Sub-label Styling**: Italic, fontSize 15, color `rgba(255, 255, 255, 0.6)`, marginTop 10. Matches spec code structure. (`ThreeComponents.tsx:65-74`)

10. **Center Code Block**: Positioned at centroid, "Generated Code" label, monospace font (fontSize 13), gray (`rgba(160, 160, 160, 0.6)`), background at 0.1 opacity, 1px border at 0.25 opacity, borderRadius 8, NO GLOW. Opacity animates from 0 to 0.5 over frames 180-220. Matches spec. (`ThreeComponents.tsx:383-406`, `constants.ts:30-31`)

11. **Derivation Arrows**: Three dashed lines from edge midpoints pointing toward centroid. Opacity animates from 0 to 0.3 over frames 200-240. Shortening logic (40% to 80%) keeps arrows subtle. Matches spec intent. (`ThreeComponents.tsx:149-173, 294-364`, `constants.ts:32-33`)

12. **Hold Phase**: Frame 240+ holds the complete diagram. Matches spec (frames 240-300 hold). (`constants.ts:36`)

13. **Integration into ClosingSection**: ThreeComponents is used as Visual 3 in the ClosingSection, triggered at approximately 13.02s. Narration aligns with "Prompts encode intent...Tests preserve behavior...Grounding maintains style". (`S06-Closing/constants.ts:43-44`, `S06-Closing/ClosingSection.tsx:58-62`)

### Issues Found

1. **Sub-label Text Mismatch (Medium)**
   - Spec says: "encodes intent", "preserves behavior", "maintains style"
   - Implementation has: "Intent", "Constraints", "Style"
   - The spec explicitly defines the sub-labels as full phrases ("encodes intent", "preserves behavior", "maintains style") and ties them to narration sync ("Each clause lands as its corresponding vertex glows brighter"). The implementation uses shortened single-word labels that do not match the narration.
   - Files: `ThreeComponents.tsx:232-234`

2. **Triangle Geometry Deviates from Spec (Medium)**
   - Spec says: `centerX = 960, centerY = 480, radius = 280`, which yields:
     - PROMPT: `{960, 200}` (480 - 280)
     - TESTS: `{717.5, 620}` (480 + 280*0.5, 960 - 280*0.866)
     - GROUNDING: `{1202.5, 620}`
   - Implementation has:
     - PROMPT: `{960, 180}` (20px higher)
     - TESTS: `{560, 700}` (157px wider, 80px lower)
     - GROUNDING: `{1360, 700}` (157px wider, 80px lower)
   - The implementation triangle is significantly larger (effective radius ~360 vs 280) and shifted downward. While this may be a deliberate aesthetic choice, it deviates from spec measurements.
   - Files: `constants.ts:44-53`

3. **Centroid Position Incorrect (Low-Medium)**
   - The true geometric centroid of the implemented triangle `{(960+560+1360)/3, (180+700+700)/3}` = `{960, 526.7}`.
   - Implementation stores CENTROID as `{960, 430}`, which is 97px above the actual centroid.
   - This means the "Generated Code" block is not truly at the centroid but is shifted upward toward the PROMPT vertex.
   - Files: `constants.ts:52`

4. **Edge Pulse Animation Missing (Medium)**
   - Spec says: "Subtle animated pulse along edges (energy flowing)"
   - Implementation has static glow intensity on edges. There is no per-frame animated pulse or energy-flowing effect along the edge paths. The glow only changes during the intensification phase (frames 120-160) and is then static.
   - Files: `ThreeComponents.tsx:91-138`

5. **Derivation Arrows Lack Arrowheads (Low)**
   - Spec says: "Three arrows from edges/vertices pointing inward toward center code"
   - Implementation uses dashed lines without arrowheads. The word "arrows" in the spec implies directional indicators (arrowheads/markers), but the implementation renders plain dashed line segments.
   - Files: `ThreeComponents.tsx:149-173`

6. **Integration Formula Not in Spec (Low -- Additive)**
   - The implementation includes an IntegrationFormula component (appearing at frames 600-660) showing "Prompt + Tests + Grounding / Intent + Constraints + Style / = Complete Specification". This is not specified in Section 6.4.
   - This is additive (not breaking) and controlled by a `showFormula` prop, but it extends beyond what the spec defines for this section.
   - Given the ThreeComponents duration is 25 seconds (750 frames) but the ClosingSection only allocates ~6 seconds (frames 391-572 = ~181 frames relative) for this visual, the formula at frame 600 may never actually appear in the closing section context.
   - Files: `ThreeComponents.tsx:176-224, 409`, `constants.ts:39-40`

7. **Duration Mismatch (Low)**
   - Spec says: "~10 seconds" (300 frames at 30fps)
   - Implementation standalone duration: 25 seconds (750 frames)
   - In closing section context: allocated ~6 seconds (13.02s to 19.06s)
   - The standalone composition is 2.5x longer than spec, though this may be intentional for reuse across sections.
   - Files: `constants.ts:5`

### Notes

- The ThreeComponents composition serves dual duty for Section 3.17 (Mold) and Section 6.4 (Closing). The sub-label changes ("Intent"/"Constraints"/"Style" instead of "encodes intent"/"preserves behavior"/"maintains style") and integration formula appear to be compromises for reuse, but they deviate from the Section 6.4 spec text.
- The ClosingSection correctly sequences ThreeComponents as Visual 3, aligned with the narration "Prompts encode intent...Tests preserve behavior...Grounding maintains style." The narration itself uses the full phrases that the spec expects as sub-labels.
- All color constants (`NOZZLE_BLUE=#4A90D9`, `WALLS_AMBER=#D9944A`, `GROUNDING_GREEN=#5AAA6E`) match the spec exactly.
- The animation timing pattern (staggered vertices -> edges draw -> glow intensifies -> sub-labels -> code appears -> arrows -> hold) follows the spec sequence precisely.
- The easing choices match spec recommendations: `easeOutBack` for vertices, `easeOutCubic` for edges and sub-labels.
- The `CENTER_Y` in constants is 440 (not 480 as spec says), confirming the geometry deviation. `constants.ts:46`
