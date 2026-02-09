# Audit: 13_prompt_governs_code.md

## Status: PASS

### Requirements Met

1. **Canvas and Background**: 1920x1080 resolution (constants.ts lines 8-9). Dark background `#1a1a2e` (PromptGovernsCode.tsx line 63 via `COLORS.BACKGROUND`). Side-by-side flex layout (lines 64-71).

2. **Prompt Document (Left)**: Compact 15-line prompt (constants.ts lines 35-51 `PROMPT_LINES` array with 15 entries, default `promptLineCount=15` on line 6). Blue glow using `#4A90D9` (`COLORS.NOZZLE_BLUE` on line 96). Pulsing glow animation with formula `0.8 + Math.sin(frame * 0.1) * 0.2` (line 12) applied as dynamic boxShadow (line 101). Line counter displays "~15 lines" (line 126).

3. **Code File (Right)**: Large code representation with `codeLineCount=200` default (line 7). `CODE_PREVIEW` in constants.ts (lines 54-203) contains a comprehensive 200-line Python implementation matching the spec's `parse_user_id` example. Gray text color via `COLORS.CODE_GRAY` (line 190). No glow on code panel -- just a subdued `#333` border (line 171). Line counter shows "~200 lines" (line 244).

4. **Minimap with Viewport Indicator**: Minimap rendered in absolute-positioned panel (lines 200-235) at right=8, top=8, width=60, background `#2A2A3E`. Contains repeating linear gradient lines simulating code density (lines 215-221). Animated viewport indicator tracks scroll position `(codeScroll / 100) * 50%` with semi-transparent blue highlight (lines 223-233). Matches spec's minimap requirement (spec lines 258-271).

5. **Scrolling Animation**: Code scroll from 0 to 100px (lines 38-44) using `Easing.inOut(Easing.quad)` matching spec's `easeInOutQuad` requirement. Applied as `translateY` transform (line 182).

6. **Size Comparison and Ratio**: "1:5 to 1:10" ratio text displayed in gold (`COLORS.RATIO_GOLD` = `#FFD700`) at font size 40 (lines 268-278). Subtitle reads "A good prompt is a fifth to a tenth the size of the code it generates" (lines 287-296), directly matching the spec's narration text.

7. **Dominance Indicator / Visual Hierarchy**: Prompt has animated pulsing glow boxShadow (line 101) while code has no glow -- only a static gray border. Clear subordination of code to prompt visually.

8. **"Governs" Arrow**: Directional arrow between prompt and code (lines 131-146) using "--->" character in blue (`COLORS.NOZZLE_BLUE`), size 48. Opacity tied to `arrowOpacity` animation.

9. **Animation Sequence**: Prompt fades in frames 0-60 with `easeOutCubic` (lines 15-20). Arrow appears frames 90-150 (lines 23-28). Code expands frames 150-360 with `easeOutCubic` (lines 31-36). Scroll animates after code appears (line 41). Ratio fades in at frame 400 (lines 47-52). Insight text at frame 500 (lines 55-60). Timings are stretched for 20-second duration vs spec's 15-second suggestion but all phases present in correct order.

10. **Prompt Content**: Matches spec's example content -- "Parse user IDs from untrusted input", "Return None on failure, never throw", "Handle unicode" plus additional lines to fill 15-line count (constants.ts lines 35-51).

11. **Code Content**: Full Python implementation with imports, docstrings, type hints, error handling, validation logic, and helper functions (constants.ts lines 54-203). Matches the spec's example of `parse_user_id` function.

12. **Insight Text**: Additional narration-aligned text "You're specifying what and why, not how. That compression matters." (lines 322) reinforces the spec's core message.

13. **S03 Integration**: PromptGovernsCode is sequenced at Visual 13 (203.48s) and Visual 14 (211.72s) in Part3MoldThreeParts.tsx (lines 138-150), aligned with narration segments [27] and [28] covering the ratio and context window topics.

### Issues Found

1. **Prompt font family mismatch**
   - **Spec says**: `fontFamily: 'JetBrains Mono'` for prompt text (spec line 207)
   - **Implementation does**: `fontFamily: "sans-serif"` for prompt text (PromptGovernsCode.tsx line 111). The code file correctly uses `JetBrains Mono` (line 189), but the prompt card does not.
   - **Severity**: Low -- cosmetic difference; code side is correct

2. **Prompt card width wider than spec**
   - **Spec says**: `width: 280` for the prompt card (spec line 196)
   - **Implementation does**: `maxWidth: 400` (PromptGovernsCode.tsx line 100), making the prompt card ~43% wider than specified
   - **Severity**: Low -- may slightly reduce the visual contrast between small prompt and large code

3. **Arrow lacks "governs" label**
   - **Spec says**: "governs" arrow or connection with emphasis on governance relationship (spec lines 32, 58, 161)
   - **Implementation does**: Plain right-arrow character without any "governs" label text (PromptGovernsCode.tsx lines 138-145)
   - **Severity**: Low -- the directional relationship is clear, but the explicit "governs" semantic is not labeled

4. **Duration 20s vs spec's 15s**
   - **Spec says**: ~15 seconds duration (spec line 5)
   - **Implementation does**: 20 seconds standalone duration (constants.ts line 5, `PROMPT_GOVERNS_DURATION_SECONDS = 20`). In S03 sequence, used across two visuals spanning ~46 seconds total.
   - **Severity**: Low -- animation phases are proportionally preserved; the S03 sequencer controls actual runtime

### Notes

All seven original audit deltas (missing minimap, missing scroll, wrong ratio text, missing pulsing glow, wrong line counts, weak visual hierarchy, weak governs arrow) have been resolved. The implementation now faithfully represents the core visual concept: a small glowing prompt on the left governing a large gray code file on the right, with minimap, scroll animation, pulsing glow, correct line counts (15 vs 200), and the explicit "1:5 to 1:10" ratio indicator matching the narration.

The four remaining issues are all low-severity cosmetic matters (prompt font, prompt width, arrow label, duration) that do not affect the scene's ability to communicate its message. The visual hierarchy, scale contrast, and ratio messaging are all correctly implemented.
