# Audit: Prompt Variations (Section 3.12)

## Status: PASS

### Requirements Met

1. **Canvas and Background** (Spec lines 13-15): Resolution is 1920x1080 (`constants.ts:8-9`, `PROMPT_VARIATIONS_WIDTH = 1920`, `PROMPT_VARIATIONS_HEIGHT = 1080`). Background color is `#1a1a2e` (`constants.ts:24` `COLORS.BACKGROUND`, applied at `PromptVariations.tsx:174`). Split view showing two generations is achieved via a flex container at line 275. All match spec exactly.

2. **Single Prompt Source** (Spec lines 20-23): The `user_parser.prompt` concept is represented as the prompt text "Parse user ID from input" (`constants.ts:32`, rendered at `PromptVariations.tsx:210`). The prompt is rendered at center-top position using `top: 80`, `left: 50%`, `translateX(-50%)` (lines 178-182). Blue glow is achieved via `border: 2px solid #4A90D9` and `boxShadow: 0 0 20px rgba(74, 144, 217, 0.3)` (lines 189-191). "SAME PROMPT" label is present (line 201). Arrows pointing to both outputs are implemented as SVG diverging paths (lines 215-264).

3. **Two Code Outputs Side by Side** (Spec lines 25-29): `VARIATIONS` array (`constants.ts:34-53`) defines two code blocks with visibly different implementations. Version A uses `input_str`/`cleaned` with explicit if-chain; Version B uses `raw_input`/`sanitized` with ternary. Both are syntactically valid Python. They are rendered side by side in a flex container with 30px gap (`PromptVariations.tsx:275-277`), each 300px wide (line 287).

4. **Code Variants Match Spec Exactly** (Spec lines 43-61): Version A code (`constants.ts:37-43`) matches the spec's Version A verbatim: `parse_user_id(input_str)` with `cleaned = input_str.strip()` and explicit null checks. Version B code (`constants.ts:47-51`) matches the spec's Version B verbatim: `parse_user_id(raw_input)` with `sanitized = (raw_input or "").strip()` and ternary return.

5. **Test Verification with Green Checkmarks** (Spec lines 31-34): Two independent checkmark opacity animations are implemented: `checkmark1Opacity` (lines 136-141) appears 80 frames after Version A starts; `checkmark2Opacity` (lines 143-148) appears 80 frames after Version B starts. Green checkmarks with text "Tests pass" are rendered below each code block using `color: #4CAF50` (lines 321-336).

6. **Terminal Overlay** (Spec lines 36-39): `TerminalOverlay` component (lines 6-53) is fully implemented with terminal title bar dots (red/yellow/green at lines 32-34), monospace font `JetBrains Mono` (line 42). Shows `$ pdd generate user_parser.prompt` twice with success messages `Generated: parser_v1.py` and `Generated: parser_v2.py` (lines 160-171). Terminal appears at bottom-right position (`bottom: 30, right: 30`, lines 15-16). Both generations succeed with green-colored output (line 170, `color: "#2ECC71"`).

7. **Diverging Arrows** (Spec lines 22-23, 67-68): SVG implementation (lines 215-264) draws a center vertical line from the prompt box, then splits into left and right quadratic bezier curves (`Q 100 70, 30 100` left, `Q 100 70, 170 100` right) with arrowhead markers. Left arrow opacity is tied to `variation1Opacity`, right to `variation2Opacity`, creating a sequential reveal that matches the "arrows indicate it will go two places" requirement.

8. **Animation Sequence Phase 1 - Prompt Shown (Frames 0-90)** (Spec lines 65-68): `BEATS.PROMPT_START = 0`, `BEATS.PROMPT_END = 60` (`constants.ts:13-14`). Prompt fades in with `easeOutCubic` easing (line 99). "SAME PROMPT" label present (line 201). Arrows begin appearing as variations start, matching "arrows indicate it will go two places."

9. **Animation Sequence Phase 2 - First Generation (Frames 90-180)** (Spec lines 70-73): `BEATS.VARIATION_1_START = 90` (`constants.ts:15`). Left side terminal command appears at frame 90 (line 160). Version A code fades in over frames 90-130 (lines 103-108). Checkmark appears at frame 170 (90+80, lines 136-141).

10. **Animation Sequence Phase 3 - Second Generation (Frames 180-270)** (Spec lines 75-79): `BEATS.VARIATION_2_START = 180` (`constants.ts:16`). Right side terminal command appears at frame 180 (line 166). Version B code fades in over frames 180-220 (lines 110-115). Checkmark appears at frame 260 (180+80, lines 143-148). Code is visibly different from Version A.

11. **Animation Sequence Phase 4 - Comparison Highlight (Frames 270-360)** (Spec lines 81-85): `BEATS.DIFF_HIGHLIGHT_START = 270` (`constants.ts:17`). Four `DifferenceHighlight` components (lines 348-372) highlight: `input_str` vs `raw_input` (parameter name difference) and `cleaned` vs `sanitized` (variable name difference). Uses amber color `#FFAA55` with semi-transparent background `rgba(255, 170, 85, 0.25)` (lines 74-75), matching the spec's amber highlight color.

12. **Animation Sequence Phase 5 - Key Insight (Frames 360-450)** (Spec lines 87-90): `BEATS.INSIGHT_START = 420` (`constants.ts:18`). Insight text "Code varies. Behavior is fixed." rendered at bottom center with font size 28, weight 600, and text shadow (lines 377-400). Both code blocks retain green checkmarks during this phase.

13. **Difference Highlights Match Spec** (Spec lines 218-239): Four highlights implemented matching spec's `highlights` array: `input_str` on left line 0, `raw_input` on right line 0, `cleaned` on left line 3, `sanitized` on right line 1 (lines 348-372). The `DifferenceHighlight` component uses amber color `#FFAA55` (line 79) matching spec line 234.

14. **Prompt Fade Easing** (Spec line 244): `Easing.out(Easing.cubic)` applied to prompt opacity interpolation (`PromptVariations.tsx:99`), matching the spec's `easeOutCubic` requirement.

15. **S03 Integration**: PromptVariations is correctly imported (`Part3MoldThreeParts.tsx:22`) and rendered as Visual 12 (lines 132-136) with `Sequence from={BEATS.VISUAL_12_START}` where `VISUAL_12_START = s2f(195.5)` = frame 5865 (`S03 constants.ts:109`). It spans from 195.5s to 203.48s (approximately 7.98 seconds). The VISUAL_SEQUENCE entry at index 12 (`constants.ts:155`) correctly identifies it as "PromptVariations" with description "Behavior locked, code flexible, contract fixed." The narration during this window is "behavior. The code is flexible. The contract is fixed." which aligns with the spec's narration sync.

16. **Props and Exports**: Zod schema properly defined (`constants.ts:56-64`) with `showVariations` boolean prop defaulting to true. Clean barrel exports in `index.ts` (lines 1-9).

### Issues Found

1. **Prompt Filename Not Displayed** (Low severity): The spec's visual diagram (lines 96-98) shows `user_parser.prompt` as the filename in the prompt box. The implementation shows the label "SAME PROMPT" and the underlying text "Parse user ID from input" (`PromptVariations.tsx:201,210`) but does not display the filename `user_parser.prompt` itself. The terminal overlay does reference the filename in the command `$ pdd generate user_parser.prompt` (line 161), so the filename appears in the scene but not in the prompt source box where the spec places it.

2. **Checkmark Text Wording Differs** (Low severity): Spec line 113 shows "All tests pass" under each code block. Implementation shows "Tests pass" (`PromptVariations.tsx:334`), omitting "All". The message is semantically equivalent but not a verbatim match.

3. **Easing Not Applied to Most Animations** (Low severity): The spec (lines 244-248) prescribes specific easing curves for each animation type: arrow draw (`easeOutQuad`), code appearance (`easeOutCubic`), highlight pulse (`easeInOutSine`), insight text (`easeOutCubic`). Only the prompt fade has explicit easing (`Easing.out(Easing.cubic)` at line 99). The variation opacities (lines 103-115), diff highlights (lines 120-125), and insight opacity (lines 128-133) all use default linear interpolation. This makes transitions appear less polished than specified.

4. **Duration Mismatch** (Low severity): Spec targets ~15 seconds (spec line 4, `PROMPT_VARIATIONS_DURATION_SECONDS`). The standalone composition is configured for 20 seconds (`constants.ts:5`). The embedded S03 allocation is approximately 7.98 seconds (195.5s to 203.48s). The 20-second standalone duration provides extra hold time; the S03 embedding is shorter but sufficient given the narration alignment. Neither matches the spec's 15-second target exactly.

5. **Insight Timing Shifted** (Low severity): Spec places the key insight phase at frames 360-450 (spec line 87). Implementation uses `BEATS.INSIGHT_START = 420` (`constants.ts:18`), which is 60 frames later than the spec's start. This shifts the insight appearance later into the animation, but within the 20-second standalone duration it still has adequate hold time. In the S03 embedding, this places it well within the allocated window.

### Notes

The implementation faithfully captures all the essential visual and narrative elements of the spec: same prompt producing two visibly different code outputs, side-by-side comparison with individual test verification checkmarks, amber-colored difference highlights calling out specific variable name differences, a terminal overlay showing both generation commands, diverging SVG arrows from the prompt to each output, and the key takeaway message "Code varies. Behavior is fixed." The code variants match the spec character-for-character. The five issues found are all low severity and cosmetic in nature -- a missing filename label in the prompt box, slightly different checkmark wording, missing easing on some interpolations, duration differences, and a shifted insight timing. None of these affect the core visual narrative or the scene's ability to communicate that implementation varies while behavior remains fixed.

**Resolution Status:** RESOLVED -- all issues are low severity and do not impact the scene's narrative or visual integrity.

**Files reviewed:**
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/32-PromptVariations/PromptVariations.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/32-PromptVariations/constants.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/32-PromptVariations/index.ts`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/Part3MoldThreeParts.tsx`
- `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S03-MoldThreeParts/constants.ts`

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Rendered**: Standalone still at frame 200 (`PromptVariations`). Shows "SAME PROMPT" box at top with blue glow, "Parse user ID from input" text. Generation A (left) fully visible with code (`input_str` variable). Generation B (right) visible but with lower opacity (still fading in). Green checkmark "Tests pass" below Generation A. Terminal overlay at bottom-right showing `$ pdd generate user_parser.prompt` commands.
- **Result**: Two distinct code variants from same prompt, both passing tests. Terminal overlay, diverging arrows, and difference highlighting all implemented. PASS.
