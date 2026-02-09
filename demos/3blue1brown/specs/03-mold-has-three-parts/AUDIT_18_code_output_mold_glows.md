# Audit: Code Output Mold Glows

## Status: RESOLVED

### Requirements Met

1. **Background color matches spec** -- Spec line 15 requires dark `#1a1a2e`. Implementation uses `COLORS.BACKGROUND` which resolves to `"#1a1a2e"` (`constants.ts` line 42, `CodeOutputMoldGlows.tsx` line 256). Exact match.

2. **Resolution matches spec** -- Spec line 14 requires 1920x1080. Constants define `CODE_OUTPUT_WIDTH = 1920` and `CODE_OUTPUT_HEIGHT = 1080` (`constants.ts` lines 8-9). Exact match.

3. **FPS is 30** -- `CODE_OUTPUT_FPS = 30` (`constants.ts` line 4). Matches the spec's frame-based timing which assumes 30fps.

4. **Duration is 20 seconds (600 frames)** -- `CODE_OUTPUT_DURATION_SECONDS = 20` (`constants.ts` line 5), yielding `CODE_OUTPUT_DURATION_FRAMES = 600` (`constants.ts` lines 6-7). Matches spec line 4 exactly.

5. **Five-phase animation sequence implemented** -- The component implements all five phases from the spec (lines 43-66):
   - Phase 1 (0-4s, frames 0-120): Code glows brightly at intensity 1.0 via `codeGlow` interpolation holding at 1 over `[0, 120]`.
   - Phase 2 (4-10s, frames 120-300): Code glow fades from 1 to 0 via `codeGlow` interpolation `[120, 300] -> [1, 0]`. Code opacity dims from 1 to 0.5 via `codeOpacity`.
   - Phase 3 (10-14s, frames 200-400): Mold glow increases from 0.5 to 1.0 via `moldGlow` interpolation with `easeOutQuad`.
   - Phase 4 (14-18s, frames 420-460): First message "The code is output." fades in via `message1Opacity`.
   - Phase 5 (18-20s, frames 540-580): Second message "The mold is what matters." fades in via `message2Opacity`. Final glow boost on mold (1.0 to 1.4).

6. **Generated code displayed as actual readable code** -- The `GeneratedCode` component renders the `GENERATED_CODE` constant (the `parse_user_id` Python function) inside a `<pre>` tag with `fontFamily: "'JetBrains Mono', monospace"` at `fontSize: 12` (`CodeOutputMoldGlows.tsx` lines 112-123). Matches spec lines 163-210.

7. **Code glow interpolation implemented** -- `codeGlow` interpolates over `[0, sf(120), sf(300)]` mapping to `[1, 1, 0]` with `Easing.in(Easing.quad)` (`CodeOutputMoldGlows.tsx` lines 196-201). Matches spec lines 101-107 (`easeInQuad` for code glow fade).

8. **Code opacity dims correctly (not inverted)** -- `codeOpacity` interpolates from `[0, sf(300)]` to `[1, 0.5]` with `Easing.in(Easing.quad)` (`CodeOutputMoldGlows.tsx` lines 205-210). Code starts fully visible at opacity 1 and dims to 0.5. Matches spec lines 109-115.

9. **Three mold components shown as separate labeled boxes** -- `MoldSystem` renders three `MiniComponent` elements in a horizontal `flex` layout with `gap: 30` (`CodeOutputMoldGlows.tsx` lines 42-76). Each `MiniComponent` displays a label ("PROMPT", "TESTS", "GROUNDING") with colored borders and individual `boxShadow` glow effects. Matches spec lines 216-269.

10. **Mold component colors match spec** -- PROMPT uses `#4A90D9` (blue), TESTS uses `#D9944A` (amber), GROUNDING uses `#5AAA6E` (green) (`constants.ts` lines 43-45). Exact match with spec lines 232-243.

11. **Mold glow timing matches spec** -- `moldGlow` interpolates over `[sf(200), sf(400)]` from 0.5 to 1.0 with `Easing.out(Easing.quad)` (`CodeOutputMoldGlows.tsx` lines 214-223). At standalone 600 frames this is frames 200-400 (6.7s to 13.3s). Matches spec lines 118-123.

12. **Message timing matches spec** -- `message1Opacity` at `[sf(420), sf(460)]` and `message2Opacity` at `[sf(540), sf(580)]` (`CodeOutputMoldGlows.tsx` lines 226-243). At standalone 600 frames this is frames 420-460 and 540-580 (14-15.3s and 18-19.3s). Matches spec lines 127-138.

13. **First message text matches spec** -- "The code is output." (`CodeOutputMoldGlows.tsx` line 265). Matches spec lines 38, 59.

14. **Second message text matches spec** -- "The mold is what matters." (`CodeOutputMoldGlows.tsx` line 266). Matches spec lines 39, 64.

15. **Message font sizes match spec** -- Line 1 at `fontSize: 24` with `color: '#888'` (`CodeOutputMoldGlows.tsx` lines 149-150). Line 2 at `fontSize: 28` with `color: '#FFF'` and `fontWeight: 'bold'` (`CodeOutputMoldGlows.tsx` lines 159-161). Matches spec lines 290-306.

16. **Message positioning matches spec** -- Messages positioned at `bottom: 60`, centered via `left: '50%'` and `transform: 'translateX(-50%)'` (`CodeOutputMoldGlows.tsx` lines 140-144). Matches spec lines 283-288.

17. **Easing functions match spec** -- `Easing.in(Easing.quad)` for code glow fade and code opacity. `Easing.out(Easing.quad)` for mold glow increase. `Easing.out(Easing.cubic)` for message fade. Matches spec lines 312-315.

18. **Value hierarchy visual shift achieved** -- Code starts at full glow and opacity (prominent, glowing), then fades and dims while mold glow increases. The viewer sees the code as initially valuable ("success" feeling) and watches the value transfer to the mold. The spec's ASCII art diagram (lines 68-93) is faithfully represented.

19. **showMessages prop functional** -- The `showMessages` prop controls whether messages render (opacity set to 0 when `showMessages` is false). `CodeOutputMoldGlows.tsx` lines 226-243.

20. **Second message text shadow using component colors** -- `textShadow` on second message uses blue, amber, and green glow colors keyed to `moldGlowIntensity` (`CodeOutputMoldGlows.tsx` lines 163-169).

21. **durationFrames prop for section integration** -- Optional `durationFrames` prop (`constants.ts` line 68) enables proportional compression of the five-phase animation when the component is embedded in shorter section contexts. All keyframes scale via `sf()` helper. This ensures both messages appear within the S03 Part3 available time (~8.67s) and the S06 Closing available time.

22. **S03 Visual 20 extended** -- `VISUAL_20_END` extended from `s2f(291.86)` to `s2f(295.0)` in `S03-MoldThreeParts/constants.ts`, giving ~260 frames (8.67s) instead of 166 frames (5.5s). The `durationFrames` prop is passed as `BEATS.VISUAL_20_END - BEATS.VISUAL_20_START` in `Part3MoldThreeParts.tsx`, compressing the full five-phase sequence to fit.

23. **S06 Closing sections pass durationFrames** -- Both Visual 4 and Visual 5 in `S06-Closing/ClosingSection.tsx` pass `durationFrames` computed from their respective BEATS ranges, ensuring proper animation scaling in their shorter windows.

24. **GENERATED_CODE constant used** -- The `parse_user_id` function defined in `constants.ts` lines 53-60 is imported and rendered by `GeneratedCode` component. No longer dead code.

### Issues Found

None. All 14 original issues (6 HIGH, 4 MEDIUM, 4 LOW) have been resolved.

### Resolution Summary

The component was fully refactored to match the spec:

1. **(MEDIUM) First message text** -- Changed from "The code is just plastic." to "The code is output." per spec.
2. **(HIGH) Duration** -- Changed from 10s (300 frames) to 20s (600 frames) per spec.
3. **(HIGH) Five-phase animation** -- Implemented all five phases with correct frame ranges and easing.
4. **(HIGH) Generated code display** -- Replaced abstract gray bars with actual readable `parse_user_id` Python code in a `<pre>` tag with JetBrains Mono font and glowing border.
5. **(MEDIUM) Labeled mold components** -- Replaced single unified shape with three separate `MiniComponent` boxes labeled "PROMPT", "TESTS", "GROUNDING" in a horizontal flex layout.
6. **(HIGH) Code glow interpolation** -- Added `codeGlow` interpolation `[0, 120, 300] -> [1, 1, 0]` with `easeInQuad`.
7. **(HIGH) Code opacity direction** -- Fixed from fading IN (0 to 0.4) to dimming OUT (1 to 0.5) per spec.
8. **(MEDIUM) Mold glow timing** -- Changed from `[0, 60]` to `[200, 400]` with `easeOutQuad` per spec.
9. **(MEDIUM) Message timing** -- Changed from `[120, 160]` / `[210, 250]` to `[420, 460]` / `[540, 580]` per spec.
10. **(LOW) Easing functions** -- All now match spec exactly.
11. **(HIGH) Value hierarchy** -- Code starts bright and dims; mold starts dim and brightens. The narrative arc is now structurally present.
12. **(LOW) Font sizes** -- Changed from 32/36 to 24/28 per spec.
13. **(LOW) showMessages prop** -- Now controls message visibility.
14. **(LOW) Message positioning** -- Changed from `bottom: 140` to `bottom: 60` with spec's centering method.

Additionally, a `durationFrames` prop was added to support proportional animation scaling when the component is embedded in shorter section contexts (S03, S06). S03 Visual 20 was extended from ~5.5s to ~8.67s to provide more screen time for the value hierarchy narrative.

## Resolution Status: RESOLVED
