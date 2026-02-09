# Audit: 01g_code_regenerates.md

## Status: RESOLVED

## Spec Summary
Code deletion and regeneration sequence (~15 seconds, 1:35-1:50):
- Patched function from 01f deletes (blue selection flash, lines sweep upward)
- Empty editor with blinking cursor hold (~1 second)
- Fresh clean code regenerates line-by-line in ~0.8 seconds
- Terminal snippet in bottom-right shows `pdd generate user_parser` with completion message
- Final hold on clean regenerated code
- Narration: "So why are we still patching?" lands during hold on clean code
- Crossfade transition to 01h title card

## Implementation Locations
The primary implementation is now a dedicated component:
1. **S00-ColdOpen/CodeRegeneratesVisual.tsx**: New standalone component implementing the full 01g spec with all seven animation phases, editor chrome, blinking cursor, multi-stage terminal, and title crossfade.
2. **S00-ColdOpen/ColdOpenSection.tsx** (VISUAL_03B, activeVisual === 5): Integrates CodeRegeneratesVisual into the section-level composition sequence at the correct timing position (after 01f CodeBlinks, before 01h title card).
3. **S00-ColdOpen/constants.ts**: Updated with VISUAL_03B timing (15 seconds, 450 frames at 30fps) and extended section duration to 54 seconds.

### Requirements Met

1. **Dark background (#1E1E2E)**: `CodeRegeneratesVisual.tsx` uses `backgroundColor: "#1E1E2E"` on the AbsoluteFill (line 535). Exact spec color.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:535`

2. **Old patched code shown (~30 lines)**: OLD_CODE_LINES array contains 33 lines of patched code matching the CodeBlinks data for visual continuity, including patch comments (`# patched: handle None input (hotfix 2024-01)`), workaround comments, and TODO markers.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:7-41`

3. **New clean code shown (~17 lines with type hints, docstring)**: NEW_CODE_LINES array contains 17 syntax-highlighted lines matching spec's `parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:` with full docstring, type hints, dictionary comprehension, and `_inner_parse` call.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:49-145`

4. **Selection flash (Phase 1, frames 0-6)**: Blue highlight (#264F78) flashes over all old code lines simultaneously with opacity 0 -> 0.4 -> 0 over 6 frames using linear easing.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:449-454,639-653`

5. **Staggered deletion sweep (Phase 2, frames 6-30)**: Lines dissolve upward with 0.5-frame stagger per line, top lines first. Each line fades opacity 1->0 and translates Y by -20px using `Easing.in(Easing.quad)` (easeInQuad). Git-blame gutter colors and warning icon fade simultaneously.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:456-613`

6. **Empty editor hold (Phase 3, frames 30-60)**: Deletion complete at frame 30, regeneration starts at frame 66. This creates a 36-frame (~1.2 second) empty editor beat with only a blinking cursor at line 47, column 1. The empty gutter background persists without line numbers. "The emptiness is the point."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:550-564,660-663`

7. **Blinking cursor**: Cursor blinks at line 47, column 0 during empty beat (frames 30-66), then at end of regenerated function (frame 90+). Blink cycle is ~0.53 seconds (~16 frames at 30fps) using alternating on/off via modular arithmetic.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:470-478,660-663,752-759`

8. **Line-by-line code regeneration (Phase 5, frames 66-90)**: Fresh code types in line by line, top to bottom. 17 lines in 24 frames (~1.41 frames per line). Each line has left-to-right character reveal with `Easing.out(Easing.cubic)` per line. Subtle blur leading edge on the reveal front.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:480-482,666-750`

9. **Multi-stage terminal progression**: Terminal window (310x auto, bg #252535, border #3a3a4a, 12px JetBrains Mono) appears at frame 30 (easeOutCubic fade-in). Three content stages: (1) `$ pdd generate user_parser` in white (#E0E0E0) from frame 30, (2) `Generating from prompt...` in gray (#888) at frame 60, (3) `Done. (0.8s) checkmark` in soft green (#5AAA6E) at frame 90. Terminal text appears instantly (no fade, mimics real terminal output).
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:388-432`

10. **Editor chrome (filename bar, gutter, line numbers)**: Full editor chrome matching CodeBlinks: EditorTopBar with window dots and `user_parser.py` filename, LineNumberGutter starting at line 47, BlameGutter with per-line colors (old code only), WarningIcon on TODO line, Scrollbar. All chrome dimensions/styling match CodeBlinks for visual continuity.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:184-366`

11. **Git-blame gutter contrast**: Old code has blame gutter colors (multi-era: #3A4A5A, #4A3A3A, #4A4A3A, #5A3A3A, #3A3A4A) that fade with deletion. New code has NO blame gutter -- "it has no history, no layers, no baggage."
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:462-468,566-569`

12. **Timing matches spec (15 seconds, 450 frames)**: VISUAL_03B spans s2f(28.78) to s2f(43.78) = 15 seconds (450 frames at 30fps). Section duration extended to 54 seconds. Seven animation phases match spec timing: selection flash (0-0.2s), delete sweep (0.2-1s), empty beat (1-2.2s), terminal activity (2-2.2s), regeneration (2.2-3s), terminal completion (3-3.2s), hold on clean code (3.2-15s).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts:49-58`

13. **Syntax highlighting on regenerated code**: NEW_CODE_LINES uses per-token syntax coloring: keywords (#C586C0 purple, #569CD6 blue), strings (#CE9178 orange), comments/docstrings (#6A9955 green), types (#4EC9B0 teal), function names (#DCDCAA yellow), base text (#C0C0C0 neutral gray).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:49-145`

14. **Easing per spec**: Selection flash uses linear (default interpolate). Delete sweep uses `Easing.in(Easing.quad)` (easeInQuad). Regeneration line reveal uses `Easing.out(Easing.cubic)` per line. Terminal fade-in uses `Easing.out(Easing.cubic)`. Terminal text appearance is instant (conditional render, no fade).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:449,594-612,685-694,393-398`

15. **Title crossfade transition**: In the final 3 seconds of the 15-second sequence (frame 360-450), the title "Prompt-Driven Development" fades in over the clean code. Code dims from 1.0 to 0.25 opacity while the title rises with easeOutCubic easing. This provides a smooth crossfade into VISUAL_04 (the full title card), avoiding a hard cut.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:484-505,764-797`

16. **Terminal uses correct command `pdd generate`**: Terminal text reads `$ pdd generate user_parser`, matching the spec's PDD Command Placement requirements.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:421`

17. **Resolution 1920x1080**: Constants define `COLD_OPEN_WIDTH = 1920` and `COLD_OPEN_HEIGHT = 1080`.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts:18-19`

### Issues Resolved

#### Issue 1: No deletion animation (selection flash + upward sweep) -- RESOLVED
- **Fix**: CodeRegeneratesVisual.tsx implements Phase 1 (selection flash, frames 0-6) and Phase 2 (staggered upward deletion, frames 6-30). Each old code line gets a blue selection flash overlay (#264F78) and then dissolves upward with per-line stagger (0.5 frames), opacity fade, and -20px Y translation using `Easing.in(Easing.quad)`. Blame gutter and warning icon fade simultaneously.

#### Issue 2: No empty editor hold -- RESOLVED
- **Fix**: Deletion completes at frame 30 and regeneration starts at frame 66, creating a 36-frame (~1.2s) empty editor hold. During this period, only the editor chrome (top bar, empty gutter background) and a blinking cursor at line 47 are visible. This implements the spec's "visual thesis: code is disposable."

#### Issue 3: No line-by-line code regeneration animation -- RESOLVED
- **Fix**: Phase 5 (frames 66-90) renders each of the 17 NEW_CODE_LINES sequentially. Each line appears with a left-to-right character reveal using per-token rendering with `Easing.out(Easing.cubic)`. A subtle blur leading edge (gradient + blur filter) accompanies the reveal front. ~1.41 frames per line.

#### Issue 4: Terminal lacks multi-stage progression -- RESOLVED
- **Fix**: TerminalSnippet component renders three stages: (1) `$ pdd generate user_parser` (#E0E0E0) visible from frame 30, (2) `Generating from prompt...` (#888) appears at frame 60, (3) `Done. (0.8s) checkmark` (#5AAA6E) appears at frame 90. Terminal has bg #252535, border #3a3a4a, 310px width, 12px JetBrains Mono. Container fades in with easeOutCubic; text lines appear instantly (conditional render).

#### Issue 5: Timing drastically compressed -- RESOLVED
- **Fix**: New VISUAL_03B beat added to constants.ts spanning 15 seconds (450 frames at 30fps). Section duration extended from 40s to 54s. The seven spec phases are implemented at their exact frame timings: selection flash (0-6), delete sweep (6-30), empty beat (30-60/66), terminal activity (60-66), regeneration (66-90), terminal completion (90-96), hold on clean code (96-450).

#### Issue 6: No editor chrome (gutter, line numbers, filename bar) -- RESOLVED
- **Fix**: CodeRegeneratesVisual includes full editor chrome matching CodeBlinks: EditorTopBar with macOS-style window dots and `user_parser.py` filename tab, LineNumberGutter with line numbers starting at 47, BlameGutter with per-line colors on old code, WarningIcon on the TODO comment line, and Scrollbar. Chrome dimensions (36px top bar, 52px gutter, 6px blame) match CodeBlinks for visual continuity.

#### Issue 7: No blinking cursor -- RESOLVED
- **Fix**: BlinkingCursor component renders a 9x20px white rectangle at the correct code position. During empty beat (frames 30-66), cursor blinks at line 47, column 0. During post-regeneration hold (frame 90+), cursor blinks at the end of the new function. Blink cycle is ~0.53 seconds (~16 frames at 30fps) using modular arithmetic.

### Issues Not Addressed (LOW severity, accepted)

#### Issue 8: Code samples differ from spec -- NOW RESOLVED
- New code matches spec exactly: type hints, docstring, dictionary comprehension, `_inner_parse` call. Old code is ~33 lines (vs spec's ~30) with patch history. The 33-to-17 line contrast is close to the spec's 30-to-15 and communicates "less code, more clarity" effectively.

#### Issue 9: No git-blame gutter contrast -- NOW RESOLVED
- Old code has blame gutter with multi-era colors that fade during deletion. New code has no blame gutter at all.

#### Issue 10: Transition to title card is not a crossfade -- NOW RESOLVED
- CodeRegeneratesVisual includes an integrated title crossfade in its final 3 seconds (frames 360-450). Code dims to 0.25 opacity while the title fades in with easeOutCubic. This provides a smooth visual transition into VISUAL_04.

#### Issue 11: No audio cues -- ACCEPTED (LOW)
- Audio cues are expected to be handled in post-production or as separate audio asset integration. The visual implementation does not block audio overlay.

#### Issue 12: Background color mismatch -- NOW RESOLVED
- CodeRegeneratesVisual uses `#1E1E2E` as its background color, matching the spec exactly.

#### Issue 13: Easing not per-spec -- NOW RESOLVED
- All easing functions now match the spec: linear for selection flash, easeInQuad for delete sweep, easeOutCubic for regeneration and terminal fade-in, instant for terminal text appearance.

#### Issue 14: Syntax highlighting missing on regenerated code -- NOW RESOLVED
- NEW_CODE_LINES uses per-token syntax coloring with keywords, strings, comments, types, and function names each in their correct spec colors.

### Notes

The implementation creates a new dedicated component `CodeRegeneratesVisual.tsx` in the S00-ColdOpen directory. This component is self-contained with all seven animation phases, editor chrome, and sub-components. It receives `localFrame` and `totalFrames` as props from the ColdOpenSection, which computes the local frame offset from `BEATS.VISUAL_03B_START`.

The old inline VISUAL_03 code regeneration logic in ColdOpenSection.tsx has been replaced. The activeVisual === 4 slot now correctly uses the `CodeBlinks` component for the 01f spec, and the activeVisual === 5 slot uses the new `CodeRegeneratesVisual` for 01g. The activeVisual === 6 slot retains the TitleCardVisual for the 01h title card.

The section duration was extended from 40s to 54s to accommodate the full 15-second code regeneration sequence while preserving the existing 10-second timing for CodeBlinks (01f) and TitleCardVisual (01h).

## Resolution Status: RESOLVED
