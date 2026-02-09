# Audit: 10_mold_to_prompt (Verilog Morphs to Prompt)

## Status: PASS

### Requirements Met

1. **Canvas and Duration**: 1920x1080, dark background (#1a1a2e) with gradient, full screen. Duration is 20 seconds (600 frames at 30fps). Constants in `constants.ts` lines 4-9 and 33.

2. **Starting State (Chip Design Context)**: All three chip-design elements are present on the LEFT side:
   - `VerilogBlock.tsx` renders syntax-highlighted Verilog code (teal keywords `#2AA198`, numbers `#B58900`) from the `VERILOG_SOURCE` constant, which contains a realistic ALU module.
   - `GateNetlist.tsx` renders AND, OR, and NOT gate symbols with wire connections between them, using teal color (`#1A7A6E`).
   - `SynopsysCheckmark.tsx` renders a single green checkmark (`#5AAA6E`) inside a circle, with a spring-based scale animation during setup.

3. **Ending State (Software/PDD Context)**: All three software elements are present on the RIGHT side:
   - Prompt document: white background, "PROMPT" title centered, body text matching the spec's example verbatim ("Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode." plus requirements bullets). Blue glow (#4A90D9) with Gaussian blur filter.
   - Software code: gray monospace text (`#A0A0A0`) with no glow, matching the spec's `parse_user_id` function exactly.
   - Test suite: three green checkmarks (`#5AAA6E`) with test names (`test_valid_input`, `test_empty_input`, `test_unicode_handling`).

4. **Three Parallel Morphs**: All three transformations run simultaneously during frames 90-240 (MORPH_START to MORPH_END), each using `Easing.inOut(Easing.cubic)`:
   - VerilogBlock morphs from LEFT position (260,180) to RIGHT position (1160,160), color transitions from dark code background to white document.
   - GateNetlist morphs from LEFT (280,560) to RIGHT (1170,620), gate symbols fade out, horizontal code bars appear, then actual code text fades in.
   - SynopsysCheckmark morphs from LEFT (280,770) to RIGHT (1170,900), single checkmark fades out, multiple checkmarks fade in.

5. **Animation Sequence Timing**: Matches spec's five-phase structure exactly via BEATS constants (`constants.ts` lines 17-29):
   - Frame 0-90: Setup with chip design elements visible.
   - Frame 90-240: Primary morph (three parallel transformations).
   - Frame 240-360: Labels appear ("PROMPT" title, code text becomes readable, test checkmarks with names).
   - Frame 360-480: Relationship established (FlowArrow from prompt to code with "generates" label).
   - Frame 480-600: Hold on final state.

6. **Blue Glow on Prompt (#4A90D9)**: Implemented in `VerilogBlock.tsx` using an SVG `feGaussianBlur` filter (`stdDeviation="10"`). Glow fades in during labels phase (frames 240-360) using `Easing.out(Easing.quad)`.

7. **Code Has No Glow**: GateNetlist renders code in `CODE_GRAY` (`#A0A0A0`) with no glow filter applied. Matches spec requirement "NO glow (value is in prompt, not code)".

8. **Flow Arrow with "generates" Label**: `FlowArrow.tsx` draws a downward arrow from the bottom of the prompt document to the top of the code block, with a draw-down animation. The "generates" label appears in italic after the arrow is drawn. Arrow uses prompt blue color (`rgba(74, 144, 217, 0.8)`) with a subtle pulse animation.

9. **Easing Functions**: All four spec-required easings are correctly applied:
   - Shape morph: `Easing.inOut(Easing.cubic)` (easeInOutCubic).
   - Color transitions: `Easing.out(Easing.quad)` (easeOutQuad).
   - Label fade-in: `Easing.out(Easing.cubic)` (easeOutCubic).
   - Glow appearance: `Easing.out(Easing.quad)` (easeOutQuad).

10. **Narration**: "This is that same transition. For software." renders at frame 360 (NARRATION_START), fading in over 40 frames with `Easing.out(Easing.cubic)`. Positioned at bottom center, white text, 36px.

11. **Context Labels**: LEFT side displays "Verilog Code", "Gate-Level Netlist", and "Synopsys Verification" in teal/green monospace text (fades out as morph begins). RIGHT side displays "Specification", "Generated Code", and "Verification Tests" in appropriate colors (fades in during labels phase).

12. **Prompt Document Design**: White background, border, sans-serif font ('Inter'), "PROMPT" title centered with letter-spacing, body text with requirements bullets. Matches spec's visual design section.

13. **Remotion Registration**: Properly registered in `Root.tsx` (line 619-628) as composition "MoldToPrompt" with correct dimensions, fps, and duration.

### Issues Found

1. **No explicit test-verification relationship indicator** (Minor): The spec says "Test suite positioned as verification layer" and "Clear visual hierarchy: prompt -> code -> verified by tests" (lines 78-80). The implementation shows the flow arrow only from prompt to code. There is no explicit arrow or connector from code to the test suite establishing the "verified by" relationship. The test suite appears below the code but lacks a visual link.

2. **No background context shift animation** (Minor): Spec Animation Element 4 describes "Chip design background fades, Abstract/digital background appears" (lines 55-57). The implementation uses a static dark gradient background throughout. The left-to-right movement of the morph elements implicitly conveys the context shift, but there is no animated background transition.

3. **Code lacks syntax highlighting** (Minor): The spec says code should have "syntax highlighted" text with "Gray with subtle highlighting" (lines 124-125). The implementation renders all code lines in uniform gray (`#A0A0A0`) without any syntax-based color differentiation.

4. **No drop shadow on prompt document**: The spec says "Border: Subtle shadow" (line 106). The implementation uses a border stroke but no SVG drop-shadow filter on the prompt document.

### Notes

The implementation has been fully rewritten from the original injection-mold metaphor to match the spec's chip-design-to-software transformation. All high-severity deltas from the original audit (wrong starting metaphor, missing third morph, missing test suite) have been resolved. The three parallel morphs (Verilog to prompt, netlist to code, checkmark to tests) correctly bridge from the chip design history sequence into the software/PDD context.

The remaining issues are all minor visual polish items that do not affect the conceptual correctness or narrative flow of the composition. The core visual story -- showing that the chip design workflow (Verilog specification, synthesized netlist, formal verification) maps directly onto the software workflow (prompt specification, generated code, test verification) -- is clearly and effectively communicated.

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/MoldToPrompt.tsx` - Main composition orchestrating three morphs, labels, narration
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/constants.ts` - BEATS timings, COLORS palette, layout configs, text content
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/VerilogBlock.tsx` - Verilog code block morphing to prompt document shape with blue glow
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/PromptDocument.tsx` - "PROMPT" title and body text appearing during labels phase
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/GateNetlist.tsx` - Gate symbols morphing to gray software code lines
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/SynopsysCheckmark.tsx` - Single checkmark splitting into test suite with green checkmarks
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/FlowArrow.tsx` - Downward arrow from prompt to code with "generates" label
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/19-MoldToPrompt/index.ts` - Barrel exports
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx` (lines 619-628) - Composition registration
