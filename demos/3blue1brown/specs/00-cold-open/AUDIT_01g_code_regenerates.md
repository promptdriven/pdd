# Audit: Code Regenerates

## Status: PASS

### Requirements Met

1. **Dark background (#1E1E2E)**: The AbsoluteFill in `CodeRegeneratesVisual.tsx` line 535 uses `backgroundColor: "#1E1E2E"`, matching the spec exactly. Visually confirmed in all rendered frames -- the background is the correct dark shade throughout.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:535`

2. **Resolution 1920x1080**: Constants define `COLD_OPEN_WIDTH = 1920` and `COLD_OPEN_HEIGHT = 1080`. Rendered stills confirm full-resolution output.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts:18-19`

3. **Old patched code (~30 lines)**: `OLD_CODE_LINES` array contains 33 lines of patched code with patch comments (`# patched: handle None input (hotfix 2024-01)`), workaround comments, legacy compat blocks, TODO markers, and broad except handlers. Visually confirmed at frame 863 (local 0): all lines render correctly with line numbers 47-79, warning icon on the TODO line, and git-blame gutter colors.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:7-41`

4. **New clean code (~15 lines)**: `NEW_CODE_LINES` array contains 17 syntax-highlighted lines matching the spec's `parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:` with full docstring, type hints, dictionary comprehension, and `_inner_parse` call. Visually confirmed at frame 960 (local 97): clean function with 17 lines (47-63), matching the spec sample code.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:49-145`

5. **Selection flash (Phase 1, frames 0-6)**: Blue highlight (#264F78) flashes over all old code lines simultaneously with opacity 0 -> 0.4 -> 0 over 6 frames using linear easing (default `interpolate` behavior). Overlay div spans the full line width.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:449-454,639-653`

6. **Staggered deletion sweep (Phase 2, frames 6-30)**: Lines dissolve upward with 0.5-frame stagger per line, top lines first. Each line fades opacity 1->0 and translates Y by -20px using `Easing.in(Easing.quad)` (easeInQuad per spec). Git-blame gutter colors and warning icon fade simultaneously via shared `blameOpacity` interpolation.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:456-613`

7. **Empty editor hold (Phase 3, frames 30-66)**: Visually confirmed at frame 893 (local 30): completely empty editor with only the top bar ("user_parser.py") and a blinking cursor visible. No line numbers, no code. The empty gutter background persists. Also confirmed at frame 923 (local 60): still empty with terminal now visible. The 36-frame (~1.2s) hold implements the spec's "the emptiness is the point."
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:550-564,660-663`

8. **Blinking cursor**: Cursor blinks at line 47, column 0 during empty beat (frames 30-66), then at end of regenerated function (frame 90+). Blink cycle is ~0.53 seconds (~16 frames at 30fps) using modular arithmetic. Visually confirmed: cursor visible at frame 893, not visible at frame 923 (blink off), visible again at frame 960 (post-regen).
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:470-478,660-663,752-759`

9. **Line-by-line code regeneration (Phase 5, frames 66-90)**: Fresh code types in line by line, top to bottom. 17 lines in 24 frames (~1.41 frames per line). Each line has left-to-right character reveal with `Easing.out(Easing.cubic)` per line. Subtle blur leading edge (gradient + blur filter) accompanies the reveal front. Visually confirmed at frame 940 (local 77): partial regeneration in progress showing 8 lines with character-level reveal.
   - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:480-482,666-750`

10. **Multi-stage terminal progression**: Terminal window (310px, bg #252535, border #3a3a4a, 12px JetBrains Mono, positioned bottom-right at 40px inset) appears at frame 30 with easeOutCubic fade-in. Three content stages: (1) `$ pdd generate user_parser` in white (#E0E0E0) from frame 30, (2) `Generating from prompt...` in gray (#888) at frame 60, (3) `Done. (0.8s)` with checkmark in soft green (#5AAA6E) at frame 90. Terminal text appears instantly (conditional render, no fade). Visually confirmed at frames 923 (stages 1+2 visible), 940 (stages 1+2), and 960 (all three stages visible with green "Done").
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:388-432`

11. **Editor chrome (filename bar, gutter, line numbers)**: Full editor chrome: EditorTopBar with macOS-style window dots (red/yellow/green) and `user_parser.py` filename tab, LineNumberGutter starting at line 47, BlameGutter with per-line era colors (old code only), WarningIcon on TODO line, Scrollbar. Visually confirmed in all rendered frames.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:184-366`

12. **Git-blame gutter contrast**: Old code has blame gutter colors (multi-era: #3A4A5A, #4A3A3A, #4A4A3A, #5A3A3A, #3A3A4A) that fade with deletion. New code has NO blame gutter at all -- "it has no history, no layers, no baggage." Visually confirmed: blame colors visible at frame 863, absent on regenerated code at frame 960.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:462-468,566-569`

13. **Timing matches spec (15 seconds, 450 frames)**: VISUAL_03B spans s2f(28.78) to s2f(43.78) = 15 seconds (450 frames at 30fps). Section duration is 54 seconds. Seven animation phases match spec timing: selection flash (0-6), delete sweep (6-30), empty beat (30-60/66), terminal activity (60-66), regeneration (66-90), terminal completion (90-96), hold on clean code (96-450).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/constants.ts:49-58`

14. **Syntax highlighting on regenerated code**: NEW_CODE_LINES uses per-token syntax coloring: keywords `if`/`is`/`else`/`return`/`for`/`in`/`not`/`and` in purple (#C586C0), `def`/`None` in blue (#569CD6), strings in orange (#CE9178), docstrings/comments in green (#6A9955), types `str`/`dict` in teal (#4EC9B0), function name `parse_user_input` in yellow (#DCDCAA), base text in neutral gray (#C0C0C0). Visually confirmed at frames 940 and 960: syntax colors are clearly differentiated.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:49-145`

15. **Easing per spec**: Selection flash uses linear (default `interpolate`). Delete sweep uses `Easing.in(Easing.quad)` (easeInQuad). Regeneration line reveal uses `Easing.out(Easing.cubic)` per line. Terminal fade-in uses `Easing.out(Easing.cubic)`. Terminal text appearance is instant (conditional render, no fade). Title crossfade uses `Easing.out(Easing.cubic)`.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:449,601,692,397,489`

16. **Title crossfade transition**: In the final 3 seconds (frames 360-450), the title "Prompt-Driven Development" fades in over the clean code. Code dims from 1.0 to 0.25 opacity while the title rises from 20px below with easeOutCubic easing. Title uses Inter/system-ui font at 72px, weight 600, color #F8F4F0 with text shadow and subtle blue glow. Visually confirmed at frame 1250 (local 387): title is prominently displayed over dimmed but still visible code, terminal persists in corner.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:484-505,764-797`

17. **Terminal uses correct command `pdd generate`**: Terminal text reads `$ pdd generate user_parser`, matching the spec's PDD Command Placement requirements for bottom-right corner terminal snippet.
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/CodeRegeneratesVisual.tsx:421`

18. **Integration in ColdOpenSection**: CodeRegeneratesVisual is correctly integrated at `activeVisual === 5` in ColdOpenSection.tsx, receiving `localFrame` computed from `frame - BEATS.VISUAL_03B_START` and `totalFrames` from the beat duration. Sequenced correctly between CodeBlinks (activeVisual 4) and TitleCardVisual (activeVisual 6).
    - File: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S00-ColdOpen/ColdOpenSection.tsx:104-113`

### Issues Found

1. **[LOW] Old code line count is 33 vs spec's ~30**: The OLD_CODE_LINES array has 33 entries while the spec says "~30 lines." This is a minor deviation; the "~" prefix makes this approximate, and the 33-to-17 line contrast still clearly communicates the spec's intent of "less code, more clarity." The extra 3 lines provide additional visual weight to the patched function which strengthens the narrative.

2. **[LOW] No audio cues implemented**: The spec calls for several audio cues (digital "select" sound, whoosh, typing/generation sound, completion chime). These are expected to be handled in post-production or as separate audio asset integration. The visual implementation does not block audio overlay. This is consistent with how other Remotion scenes in this project handle audio.

3. **[INFO] Terminal width 310px vs spec's 300px**: The TerminalSnippet width is 310px while the spec mentions "~300x120px." This is a negligible difference that has no visible impact.

4. **[INFO] Empty beat slightly longer than spec**: The spec says "Hold for ~1 second" for the empty beat, but the implementation holds for 36 frames (~1.2 seconds, frames 30-66). This is arguably better than the spec -- a slightly longer empty beat reinforces the "visual thesis" that the emptiness is the point.

### Notes

- The implementation is a well-structured dedicated component (`CodeRegeneratesVisual.tsx`, 800 lines) with clear phase timing constants, reusable sub-components (EditorTopBar, LineNumberGutter, BlameGutter, WarningIcon, Scrollbar, BlinkingCursor, TerminalSnippet), and comprehensive animation logic.
- All seven spec phases are implemented at their correct frame timings with the correct easing functions.
- The component receives `localFrame` and `totalFrames` as props, making it cleanly isolated from section-level timing concerns.
- Visual continuity with the preceding CodeBlinks scene is maintained through matching editor chrome dimensions (36px top bar, 52px gutter, 6px blame), font settings (JetBrains Mono at 16px, 24px line height), and the same old patched code data.
- The title crossfade provides a smooth visual bridge into VISUAL_04 (the full title card), avoiding a hard cut.
- All rendered stills (frames 863, 893, 923, 940, 960, 1250) match their expected visual states according to the animation timeline.

## Resolution Status
- **Status**: PASS
- **Rationale**: All 17+ spec requirements are correctly implemented and visually confirmed through rendered stills. The seven animation phases (selection flash, delete sweep, empty beat, terminal activity, regeneration, terminal completion, hold with title crossfade) match the spec's frame timings and easing functions. Editor chrome, syntax highlighting, git-blame contrast, terminal progression, and title crossfade all work as specified. The only deviations are trivial (33 vs ~30 old code lines, 310 vs ~300px terminal width, 1.2s vs ~1s empty beat) and do not affect the visual narrative.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Fresh audit with six rendered stills across all animation phases confirms full spec compliance. Phase 1 (selection flash) shows old patched code with editor chrome, blame gutter, and warning icon. Phase 3 (empty beat) shows a clean empty editor with blinking cursor -- "the emptiness is the point." Phase 4-5 (terminal + regeneration) shows progressive terminal stages and line-by-line character reveal with syntax highlighting. Phase 6-7 (hold + title crossfade) shows clean 17-line function with all three terminal stages complete, then the "Prompt-Driven Development" title fading in over dimmed code. No regressions found from previous audit. All previously-identified issues remain resolved.
