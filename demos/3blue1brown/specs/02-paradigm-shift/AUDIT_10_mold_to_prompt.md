# Audit: 10_mold_to_prompt.md

## Spec Summary
The Verilog code morphs into a glowing document labeled "PROMPT", the gate-level netlist morphs into lines of software code, and the Synopsys verification checkmark morphs into a test suite with green checkmarks. This bridges the chip design metaphor directly to software/PDD. Duration: ~20 seconds.

## Implementation Status
**Partially Implemented** - The MoldToPrompt component implements a similar transformation but from a different starting point (injection mold → prompt rather than Verilog → prompt).

## Deltas Found

### Starting Visual Context
- **Spec says**: "Starting State: Verilog code (from chip design sequence), Gate-level netlist below/beside it, Synopsys verification checkmark, Chip design / EDA context" (lines 21-26)
- **Implementation does**: Starting state is an injection mold (metallic shape with cavity) and amber plastic part, not Verilog/netlist/checkmark (MoldToPrompt.tsx:55-98, MoldShape.tsx:114-196)
- **Severity**: High - Completely different starting point, breaks continuity from chip design sequence

### Verilog Code → Prompt Document Morph
- **Spec says**: "Verilog code reshapes into rectangular document, Code syntax → Clean specification text, 'PROMPT' label appears" (lines 36-40)
- **Implementation does**: Injection mold (metallic gradient) morphs to white document with "PROMPT" label (MoldShape.tsx:1-196, PromptDocument.tsx:1-111)
- **Severity**: High - Source material is completely different (mold vs. Verilog)

### Gate-Level Netlist → Software Code Morph
- **Spec says**: "Netlist diagram stretches into horizontal lines, Gate symbols → Monospace text, Software code syntax visible" (lines 42-46)
- **Implementation does**: Amber plastic part morphs into gray code lines with proper monospace text (CodeLines.tsx:1-186)
- **Severity**: Medium - The target (code lines) is correct, but source (plastic part vs. netlist) differs

### Synopsys Checkmark → Test Suite Morph
- **Spec says**: "Verification checkmark splits into multiple checkmarks, Single formal proof → Multiple test cases" (lines 48-52)
- **Implementation does**: No checkmark morph present in MoldToPrompt component
- **Severity**: High - Missing entirely; test suite concept not introduced here

### Prompt Document Content
- **Spec says**: Example prompt text about "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." with requirements bullets (lines 91-102)
- **Implementation does**: PROMPT_LINES constant provides prompt text (constants file), includes requirements format (PromptDocument.tsx:72-107)
- **Severity**: Low - Content may differ but structure is correct

### Blue Glow on Prompt
- **Spec says**: "Blue (#4A90D9) soft outer glow" on prompt document (line 107)
- **Implementation does**: Blue glow implemented using COLORS.PROMPT_GLOW filter on prompt document (MoldShape.tsx:60-70, 140-154)
- **Severity**: None - Correctly implemented

### Code Has No Glow
- **Spec says**: "NO glow (value is in prompt, not code)" (line 126)
- **Implementation does**: Code lines have no glow, rendered in gray (CodeLines.tsx:103-185)
- **Severity**: None - Correctly implemented

### Flow Arrow from Prompt to Code
- **Spec says**: "Arrow or flow indicator from prompt to code, 'generates' label (optional)" (lines 77-79, 195-206)
- **Implementation does**: FlowArrow component with downward arrow and "generates" label in italic (FlowArrow.tsx:1-133)
- **Severity**: None - Correctly implemented

### Color Coding
- **Spec says**: Prompt=Blue (#4A90D9), Tests=Amber (#D9944A), Code=Gray (#A0A0A0) (lines 115-121)
- **Implementation does**: Prompt uses PROMPT_GLOW (blue), Code uses CODE_GRAY, but no tests/amber in this component
- **Severity**: Medium - Tests not present in this component (they appear in PromptGeneratesCode)

### Morph Animation Technique
- **Spec says**: "Interpolate between Verilog code block and prompt document shape" using interpolatePath and interpolateColors (lines 130-166)
- **Implementation does**: Interpolates dimensions, colors, and properties but not using path morphing (MoldShape.tsx:26-32, 34-57)
- **Severity**: Low - Different technique but achieves similar visual result

### Animation Timing
- **Spec says**: Frame 0-90 setup, 90-240 morph, 240-360 labels, 360-480 relationship, 480-600 hold (lines 61-86)
- **Implementation does**: Uses BEATS constants with similar structure (MoldToPrompt.tsx:23-36, constants file)
- **Severity**: None - Timing structure is appropriate

### Narration
- **Spec says**: "This is that same transition. For software." lands as transformation completes and "PROMPT" is visible (lines 176-178)
- **Implementation does**: Narration "This is that same transition. For software." fades in at BEATS.NARRATION_START (MoldToPrompt.tsx:100-127)
- **Severity**: None - Correctly implemented

### Manufacturing Context Label
- **Spec says**: Not specified
- **Implementation does**: "Injection Mold" label fades in during setup and out during morph (MoldToPrompt.tsx:75-98)
- **Severity**: None - Contextual addition consistent with starting visual (mold)

## Missing Elements

### Three Parallel Morphs
- **Spec says**: "Three parallel morphs (Verilog→prompt, netlist→code, checkmark→tests) reinforce the analogy" (line 228)
- **Implementation does**: Only two morphs present (mold→prompt, part→code). No checkmark→tests morph.
- **Severity**: High - The test suite transformation is missing

### Chip Design / EDA Visual Context
- **Spec says**: Starting from "Verilog code, gate-level netlist, and Synopsys verification checkmark" from chip design context (lines 21-26)
- **Implementation does**: Starts from injection molding context (mold + plastic part)
- **Severity**: High - Breaks the narrative continuity from the chip design sequence

### Test Suite with Green Checkmarks
- **Spec says**: "Test suite with green checkmarks" as ending state element (line 31, 52)
- **Implementation does**: No test suite visualization in MoldToPrompt component
- **Severity**: High - Tests are a core element of the "three parts of the mold" framework

### Relationship Indicator for Tests
- **Spec says**: "Test suite positioned as verification layer, Clear visual hierarchy: prompt -> code -> verified by tests" (lines 217-218)
- **Implementation does**: Only prompt→code relationship shown
- **Severity**: High - Tests/verification layer not introduced here

## Notes

**Critical Finding**: The MoldToPrompt component implements a different conceptual transition than what the spec describes:

**Spec Intent**: Verilog/chip-design → Prompt/software (direct mapping)
- Verilog code → Prompt document
- Gate netlist → Software code
- Synopsys checkmark → Test suite
- Three parallel transformations showing the analogy

**Implementation Reality**: Injection-molding → Software (metaphorical mapping)
- Injection mold → Prompt document
- Plastic part → Software code
- Two parallel transformations
- Manufacturing metaphor rather than direct chip-design transition

This suggests one of two possibilities:
1. The spec was written after/independently of the implementation and describes a different vision
2. The implementation predates this spec and uses a different metaphorical approach

The injection molding metaphor may actually be more accessible to general audiences (fewer people understand Verilog than understand injection molding), but it creates discontinuity with the detailed chip design history sequence (specs 09a-09e).

The test suite element is completely absent from MoldToPrompt but appears later in PromptGeneratesCode, suggesting the framework's "three parts" (prompt, code, tests) are introduced incrementally rather than all at once as the spec envisions.

**Verdict**: While the implementation is well-executed for what it does (mold→prompt morph), it does not match the spec's vision of a direct chip-design-to-software transformation with three parallel morphs. This is a fundamental conceptual delta, not just an implementation detail.
