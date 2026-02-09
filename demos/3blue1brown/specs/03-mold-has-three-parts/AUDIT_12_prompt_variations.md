# Audit: 12_prompt_variations.md

## Spec Summary
Shows the same prompt generating two different but valid code implementations. Both versions pass tests, demonstrating that "code varies, behavior is fixed." Should include terminal commands showing `pdd generate` running twice, difference highlights between versions, and green checkmarks for both.

## Implementation Status
Implemented

## Deltas Found

### Missing Terminal Overlay
- **Spec says**: Lines 37-39 and 202-211 require terminal overlay showing `pdd generate user_parser.prompt` command running twice with different timestamps/seeds
- **Implementation does**: No terminal/command line interface visible in the implementation - only shows the variations and checkmarks
- **Severity**: Medium

### Missing Difference Highlights
- **Spec says**: Lines 81-88, 216-239 specify highlighting specific differences like "input_str" vs "raw_input", "cleaned" vs "sanitized" with amber highlight boxes (#FFAA55)
- **Implementation does**: Shows two complete code blocks side by side but does NOT visually highlight the differences between them
- **Severity**: Medium

### Missing Diverging Arrows
- **Spec says**: Lines 98-99 show arrows diverging from single prompt to two outputs, line 169 includes `<DivergingArrows>` component
- **Implementation does**: Lines 83-105 show simple downward arrows (↓) but not diverging path visualization from one source to two destinations
- **Severity**: Low

### Simplified Code Variations
- **Spec says**: Lines 42-62 show two distinct code implementations with different variable names (`input_str` vs `raw_input`), different structure (if-chains vs ternary), both explicitly shown
- **Implementation does**: Lines 3 imports `VARIATIONS` from constants file - actual code content not visible in this file, but structure supports two variations
- **Severity**: None (implementation detail in constants)

### Missing "Generation A" / "Generation B" Labels
- **Spec says**: Lines 102-112 show containers labeled "Generation A" and "Generation B"
- **Implementation does**: Lines 136-137 use generic `variation.label` from constants - likely implements but label text not confirmed
- **Severity**: Low

### Checkmark Timing
- **Spec says**: Lines 177-178 show checkmarks appearing at different times (frame > 170 for A, frame > 260 for B)
- **Implementation does**: Lines 189-204 show single checkmark appearing for both simultaneously controlled by `insightOpacity`
- **Severity**: Low

## Missing Elements
1. Terminal overlay with `pdd generate` commands
2. Difference highlight boxes on specific variable names/structures
3. Diverging arrow visual (one source → two paths)
4. Separate checkmark timing for each variation

## Additional Notes
The core concept is implemented well: same prompt at top, two different code outputs below, insight text "Code varies. Behavior is fixed." with checkmarks. The missing elements are primarily enhancement details (terminal commands, difference highlights) that would strengthen the demonstration but aren't critical to the message. The implementation is functional but less detailed than the spec envisions.
