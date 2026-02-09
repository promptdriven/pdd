# Audit: 17_three_components.md

## Spec Summary
Shows all three components (Prompt, Tests, Grounding) working together in an integrated system. The animation pulls back to show the full mold system with prompt flowing in, transforming through grounding, being constrained by walls, and producing code output. Ends with an integration formula showing how the three components combine.

## Implementation Status
Partially Implemented

## Deltas Found

### Completely different visual approach: triangle vs vertical flow
- **Spec says**: Lines 75-110 show a vertical flow diagram with nozzle at top (PROMPT), grounding in middle, test walls constraining sides, and code output at bottom - representing the injection mold metaphor
- **Implementation does**: Lines 177-351 show a triangular layout with three vertices (PROMPT top, TESTS bottom-left, GROUNDING bottom-right) connected by edges, with code at the centroid - representing a dependency graph
- **Severity**: High - Fundamentally different visual metaphor. Spec uses vertical mold injection, implementation uses triangular relationship diagram

### Missing flow animation through system
- **Spec says**: Lines 48-68 describe "Prompt enters (blue glow at nozzle)", "Through grounding (green glow, material transforms)", "Constrained by walls (amber walls glow, material hits boundaries)", "Code emerges (output appears at bottom)"
- **Implementation does**: No flow animation exists. Components appear in sequence (lines 188-194 staggered vertex appearance), edges connect (lines 198-202), but no material/data flowing through the system
- **Severity**: High - Missing the core animation of how data flows through the system

### Integration formula missing
- **Spec says**: Lines 69-72 and 290-313 specify displaying "Prompt + Tests + Grounding", "Intent + Constraints + Style", "= Complete Specification" with colored text
- **Implementation does**: No formula or text labels appear in the code. There's a `showFormula` prop (constants.ts line 65) but it's never used in the component
- **Severity**: High - Missing the key conceptual takeaway message

### Component labels don't match spec
- **Spec says**: Lines 33-40 specify labels as "PROMPT" → "Intent", "TESTS" → "Constraints", "GROUNDING" → "Style"
- **Implementation does**: Lines 182-184 show labels as "PROMPT" → "encodes intent", "TESTS" → "preserves behavior", "GROUNDING" → "maintains style" (different phrasing, different semantic framing)
- **Severity**: Medium - Different conceptual framing, more implementation-focused vs user-focused

### Timeline completely different
- **Spec says**: Lines 44-72 show 4-second phases: system overview (0-4s), prompt enters (4-8s), through grounding (8-12s), constrained by walls (12-16s), code emerges (16-20s), formula (20-25s)
- **Implementation does**: constants.ts shows: vertices appear in first 50 frames (0-1.7s), edges connect (2-4s), glows intensify (4-5.3s), code appears (6-7.3s), then hold. No phase matches the spec timing
- **Severity**: Medium - Compressed timeline changes the pacing and emphasis

### Code block has no success indicators
- **Spec says**: Line 67 "Success indicator" when code emerges
- **Implementation does**: Lines 324-348 show code block with gray styling and "Generated Code" label, but no success indicator (checkmark, green color, etc.)
- **Severity**: Low - Missing positive feedback

### Missing mold walls visualization
- **Spec says**: Lines 93-96 show ASCII art with test walls `█` constraining the code space
- **Implementation does**: TESTS vertex is just a labeled node, no wall visualization
- **Severity**: Medium - Loses the physical constraint metaphor

### Missing flow arrows between components
- **Spec says**: Lines 182 and 195 show `<FlowArrow from="prompt" to="grounding" />` and similar for other connections
- **Implementation does**: Triangle edges (lines 262-294) are static connections, not directional flow arrows with animation
- **Severity**: Medium - Shows relationships but not process flow

### Center code lacks prominence
- **Spec says**: Lines 209-213 suggest code output is a significant visual element at bottom
- **Implementation does**: Lines 324-348 show code as dim, semi-transparent (opacity 0.5), with explicit note "NO GLOW" in comment on line 324
- **Severity**: Low - Code is de-emphasized, but this might be intentional for "the mold matters" message

## Missing Elements

### ComponentBlock usage different from spec
Spec lines 175-179, 186-192, 199-204 show ComponentBlock as a generic component used for all three types. Implementation has VertexNode (lines 24-76) which is similar but part of a triangle layout, not a flow layout.

### WallsBlock component
Spec lines 197-204 reference a `<WallsBlock>` component specifically for the test walls. Implementation just has another VertexNode.

### OutputBlock component
Spec lines 210-213 reference an `<OutputBlock>` component. Implementation inlines the code block (lines 324-348).

### IntegrationFormula component
Spec lines 217 and 275-313 reference an `<IntegrationFormula>` component with color-coded text. This is completely missing from implementation despite a `showFormula` prop existing.

### Prompt/Nozzle visual representation
Spec line 177 calls for "Prompt/Nozzle" visualization. Implementation only has a labeled box, no nozzle shape.

### Grounding material representation
Spec line 187 calls for visual representation of "Grounding" as material filling space. Implementation only has a labeled box.

## Positive Notes
- Three components are all present with correct colors
- Staggered animation creates nice sequential reveal
- Triangle edges with gradients are visually appealing
- Easing includes nice overshoot on vertices (back easing)
- Color palette is correct and consistent
- Duration matches spec (25 seconds)
- Derivation arrows pointing to center are a nice touch
- Code is properly de-emphasized to support "mold matters" theme
- Sub-labels add explanatory context

## Critical Note
This implementation chose a fundamentally different visual metaphor (triangle graph vs vertical flow mold). While the triangle effectively shows the three-way relationship, it loses the injection mold metaphor that's central to the video's narrative. The missing integration formula also removes the key conceptual takeaway.

---

## Resolution Status (2026-02-08)

### Fixed Issues

1. **Component labels updated** (Medium severity)
   - Changed from "encodes intent", "preserves behavior", "maintains style" to "Intent", "Constraints", "Style"
   - Now matches spec lines 33-40
   - File: ThreeComponents.tsx lines 181-185

2. **Integration formula added** (High severity)
   - Added IntegrationFormula component showing:
     - "Prompt + Tests + Grounding" (color-coded)
     - "Intent + Constraints + Style"
     - "= Complete Specification"
   - Appears at frame 600-660 (20-22s) as specified in spec lines 69-72
   - Uses `showFormula` prop from constants (line 65)
   - File: ThreeComponents.tsx lines 177-227, 398

3. **Timing constants added**
   - Added FORMULA_START: 600, FORMULA_END: 660 to BEATS
   - File: constants.ts lines 40-41

### Remaining Issues

**Note**: This composition serves DUAL purposes for TWO different sections:
- Section 3.17 (Mold): Requires vertical flow/mold metaphor with flow animation
- Section 6.4 (Closing): Requires triangle diagram (IMPLEMENTED)

The current implementation fulfills the **Section 6.4 (Closing)** requirements but does NOT fulfill Section 3.17 (Mold) requirements:

1. **Fundamentally different visual approach** (High severity - UNFIXED)
   - Spec 3.17 calls for vertical mold injection system
   - Implementation uses triangle layout (correct for Section 6.4)
   - Would require separate composition for Section 3.17

2. **Missing flow animation** (High severity - UNFIXED)
   - Spec 3.17 requires material flowing through system
   - No flow animation exists (static triangle is correct for Section 6.4)

3. **Missing mold walls visualization** (Medium severity - UNFIXED)
   - Spec 3.17 shows test walls as physical constraints
   - Implementation just has labeled vertex (correct for Section 6.4)

### Recommendation

The 37-ThreeComponents composition should be used ONLY for Section 6.4 (Closing/Triangle). A separate composition (e.g., "37b-MoldIntegration") should be created for Section 3.17 (Mold) with:
- Vertical flow layout matching lines 75-110
- Flow animation showing material moving through system
- Mold walls visualization
- The integration formula (now implemented)
