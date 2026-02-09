# Audit: 13a_context_window_comparison.md

## Spec Summary
Side-by-side comparison of two identical-sized context windows (15K tokens each). LEFT: dense raw code representing ~1 module. RIGHT: clean natural language prompts representing ~10 modules. Emphasizes information density advantage of natural language, with "Same tokens. 10x the system knowledge." Key distinction from Section 1.6: this is about DENSITY and READABILITY within a fixed window, not about window size over growing codebase.

## Implementation Status
Partially Implemented - Different Concept

## Deltas Found

### Completely Different Left Side Content
- **Spec says**: Lines 20-28 require LEFT window showing "15,000 tokens of code" - dense monospace code filling entire window, syntax-highlighted, overwhelming wall of text, labeled "~1 module"
- **Implementation does**: Lines 234-354 show LEFT window labeled "Agentic Patching" with code plus RED "IRRELEVANT" overlays and tiny GREEN "relevant" sections - this is about relevance filtering, not raw density
- **Severity**: High

### Completely Different Right Side Content
- **Spec says**: Lines 29-38 require RIGHT window showing "15,000 tokens of prompts" - ten clearly labeled prompt sections with module headers, natural language descriptions, labeled "~10 modules"
- **Implementation does**: Lines 356-504 show RIGHT window labeled "PDD Regeneration" with colored blocks (Prompt 300 tokens, Tests 2,000 tokens, Grounding Example) and "Room to think" empty space
- **Severity**: High

### Different Token Counts
- **Spec says**: Both windows are 15,000 tokens (lines 9, 43-44)
- **Implementation does**: LEFT is 15,000 tokens, RIGHT is 2,300 tokens (lines 16-17, 506-548) - not the same size
- **Severity**: High

### Different Core Message
- **Spec says**: Lines 48-50, 134 message is "Same tokens. 10x the system knowledge." emphasizing DENSITY of natural language vs code
- **Implementation does**: Lines 552-593 message is "6.5x fewer tokens" and "10x more system knowledge" - about EFFICIENCY of PDD vs agentic patching, not density comparison
- **Severity**: High

### Different Visual Metaphor
- **Spec says**: This is a MATERIAL PROPERTIES comparison - what you can FIT in the same space
- **Implementation does**: This is a METHODOLOGY comparison - agentic patching (cluttered, irrelevant) vs PDD (clean, relevant)
- **Severity**: High

### Missing Research Citation
- **Spec says**: Lines 54-55, 89-92, 271-280 require citation "NL comments improved generation +41% (UC Berkeley, 2024)" and "Author-defined context, not machine-assembled"
- **Implementation does**: No research citations visible in implementation
- **Severity**: Medium

### Missing Module Headers in Right Window
- **Spec says**: Lines 361-381, 390-402 show ten module sections with headers like "## user_parser", "## auth_handler", etc.
- **Implementation does**: Shows three categorical blocks (Prompt/Tests/Grounding) with token counts, not module-level breakdown
- **Severity**: High

### Different Animation Focus
- **Spec says**: Lines 59-100 focus on building both windows simultaneously to emphasize "same size, different content"
- **Implementation does**: Lines 36-152 focus on highlighting irrelevant vs relevant code, then showing clean alternative
- **Severity**: High

## Missing Elements
1. Dense raw code filling left window (replaced with "irrelevant" overlay concept)
2. Ten module prompt sections in right window (replaced with three block categories)
3. "15,000 tokens" for BOTH windows (right is only 2,300)
4. "Same tokens. 10x the system knowledge." message (replaced with efficiency comparison)
5. Research citations about NL comments improving generation
6. Emphasis on information DENSITY within fixed capacity
7. "Author-defined context, not machine-assembled" message
8. Left window feeling "overwhelming, wall of text" vs right feeling "organized, scannable"

## Additional Notes
**This is a fundamentally different composition** from what the spec describes. The spec wants to show:
- "Within the SAME 15K token budget, you can fit 1 module of code OR 10 modules of prompts"
- Natural language is more token-efficient for LLMs
- Leverages model training (30x more NL than code)

The implementation shows:
- "Agentic patching uses 15K tokens (mostly irrelevant) vs PDD uses 2.3K tokens (all relevant)"
- PDD is more efficient methodology
- Context relevance quality, not information density

These are **different arguments**. The spec is making a TECHNICAL point about token economics and model training. The implementation is making a WORKFLOW point about methodology effectiveness. The spec appears to have been repurposed for a different message entirely, possibly because this "agentic patching vs PDD" comparison was deemed more valuable for the demo.

**Recommendation**: This should likely be renamed or the spec should be updated to match, as they're fundamentally different sections addressing different points in the argument.
