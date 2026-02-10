# Audit: Long Prompt Display (Section 4.6)

## Status: RESOLVED

### Requirements Met

1. **Canvas and resolution**: 1920x1080 confirmed in `constants.ts:8-9` (`LONG_PROMPT_WIDTH`, `LONG_PROMPT_HEIGHT`). Dark background `#1a1a2e` applied via `COLORS.BACKGROUND` in `constants.ts:29` and used in `LongPrompt.tsx:292`.

2. **Duration**: Standalone composition is 15 seconds (450 frames at 30fps), matching the spec's "~15 seconds" (`constants.ts:4-7`). Composition registered in `Root.tsx:895-903` with correct duration, fps, and dimensions. When embedded in S04-PrecisionTradeoff, it occupies VISUAL_04 at 26.72s-35.28s (~8.5 seconds synced to narration), which is shorter than the standalone duration (see Issues).

3. **Prompt file display**: File rendered with filename `parser_v1.prompt` (`LongPrompt.tsx:295`), blue header accent `#4A90D9` (`constants.ts:30`, `LongPrompt.tsx:40`), and syntax-highlighted content. Content matches the spec's sample prompt exactly (User ID Parser - Version 1, all sections: Purpose, Input Handling, Validation Rules, Unicode Support, Error Handling, Edge Cases, Performance, Return Value, Logging) (`constants.ts:40-90`).

4. **Line count indicator**: Dynamically computed from `PROMPT_CONTENT.split("\n").length` (`LongPrompt.tsx:289`) rather than hardcoded to 50. The actual content is 51 lines, consistent with the spec's "~50 lines". A `LineCountBadge` component (`LongPrompt.tsx:217-253`) displays the count as a styled badge. The header also shows the count as "{lineCount} lines" text (`LongPrompt.tsx:64-66`). Spec's "[50L]" badge and "50 lines" badge are both covered.

5. **Content scroll**: `scrollProgress` interpolates from 0 to 0.6 over frames 60-180 (`LongPrompt.tsx:269-278`) using `Easing.inOut(Easing.quad)`, matching the spec's `easeInOutQuad` for smooth reading pace (`constants.ts:22-23`). Visible window of 25 lines (`LongPrompt.tsx:21`) scrolls through content. Scroll indicator bar appears during scrolling (`LongPrompt.tsx:119-144`). Timing compressed from original 90-270 to fit within the ~256 internal frames available in section context.

6. **Syntax highlighting**: Three-tier coloring implemented (`LongPrompt.tsx:91-95`): headers starting with `#` in blue `#4A90D9`, bullet lines starting with `-` in orange `#D9944A`, and regular text in `rgba(255, 255, 255, 0.8)`. Matches the spec's color rules exactly. Headers also rendered bold (`LongPrompt.tsx:98`).

7. **Test walls (few)**: 3 amber (`#D9944A`) walls rendered on the right side via `TestWallsSmall` component (`LongPrompt.tsx:156-210`) with `count={3}` (`LongPrompt.tsx:308`). Positioned at `x: 1450, y: 350` (`LongPrompt.tsx:310`). Walls fade in over frames 190-230 with `Easing.out(Easing.cubic)` (`LongPrompt.tsx:281-286`, `constants.ts:24-25`), using the spec's `easeOutCubic` easing. Timing compressed from original 270-330 to fit within the ~256 internal frames available in the section context, ensuring walls are fully visible before the component unmounts. Wall label displays "{count} tests" (`LongPrompt.tsx:205`), matching the spec's "3 tests" label. The `showTestWalls` prop (`LongPrompt.tsx:256, 306`) allows toggling walls.

8. **Fade indicator**: Bottom fade gradient from `transparent` to `#1E1E2E` at 80px height (`LongPrompt.tsx:107-116`), matching the spec's visual description exactly.

9. **Animation sequence**: All four phases implemented correctly in `constants.ts:17-29` (compressed to fit ~256-frame section allocation):
   - Frames 0-60: Container fades in with `easeOutCubic` (`LongPrompt.tsx:261-265`)
   - Frames 60-180: Content scrolls with `easeInOutQuad` (`LongPrompt.tsx:269-278`)
   - Frames 190-230: Test walls fade in with `easeOutCubic` (`LongPrompt.tsx:281-286`)
   - Frames 240+: Hold with all elements visible (`constants.ts:28`)

10. **Easing functions**: All three easing types match spec:
    - Container fade-in: `Easing.out(Easing.cubic)` = `easeOutCubic` (`LongPrompt.tsx:265`)
    - Scroll: `Easing.inOut(Easing.quad)` = `easeInOutQuad` (`LongPrompt.tsx:277`)
    - Walls fade-in: `Easing.out(Easing.cubic)` = `easeOutCubic` (`LongPrompt.tsx:285`)

11. **Background colors**: Main background `#1a1a2e` (`constants.ts:29`), content area `#1E1E2E` (`constants.ts:32`), both matching spec exactly.

12. **Narration sync caption**: Caption text at bottom reads "With few tests, your prompt needs to specify everything." (`LongPrompt.tsx:339`), matching the narration sync content from the spec. Fades in after walls appear (`LongPrompt.tsx:323-327`).

13. **Component integration**: Properly imported and used in `Part4PrecisionTradeoff.tsx:15,69` at VISUAL_04 slot with default props. Also registered as standalone `<Composition>` in `Root.tsx:894-903`.

14. **Code display positioning**: Prompt file container positioned at left: 150, top: 100, width: 1100 (`LongPrompt.tsx:29-31`), broadly matching the spec's centered code display layout. Test walls on the right side.

15. **Props schema**: Zod-based schema with `showTestWalls` boolean prop (`constants.ts:93-101`), exported via `index.ts`.

### Issues Found

1. **MEDIUM -- Test walls never visible in section composition**: ~~The LongPrompt component is allocated approximately 256 internal frames (~8.5 seconds) within Part4PrecisionTradeoff. The `<Sequence from={802}>` resets the child's frame counter to 0 at global frame 802. The `activeVisual` logic (`Part4PrecisionTradeoff.tsx:23-29`) switches from visual 4 to visual 5 at global frame 1058 (VISUAL_05_START), giving the LongPrompt only internal frames 0-256. The test walls begin fading in at internal frame 270 (`constants.ts:20`), which corresponds to global frame 1072 -- but the component is already unmounted at global frame 1058.~~ **RESOLVED**: Compressed all internal BEATS timings to fit within the ~256 available frames. Container fade: 0-60 (was 0-90). Scroll: 60-180 (was 90-270). Wall fade: 190-230 (was 270-330). Hold: 240+ (was 360+). Test walls are now fully visible by frame 230, with 26 frames of hold time before the component unmounts at frame 256. Scroll completes fully at frame 180. The standalone 450-frame composition still works naturally since all phases complete early with a long hold.

2. **LOW -- Test wall position shifted**: Implementation uses `x: 1450` (`LongPrompt.tsx:310`) vs spec's `x: 1400` (spec line 187). A 50px rightward shift. Walls remain on the right side as intended.

3. **LOW -- Container and content height differ from spec**: Implementation uses height 850/750 (`LongPrompt.tsx:33, 76`) vs spec's 800/700 (spec lines 219-220, 254). Each is 50px taller, proportionally consistent, accommodating more visible lines.

4. **LOW -- Test wall dimensions differ from spec**: Implementation uses 50x70 with borderRadius 6 (`LongPrompt.tsx:174-177`) vs spec's 40x60 with borderRadius 4 (spec lines 303-306). Walls are ~25% larger. They remain visually small and sparse as intended.

5. **LOW -- Unicode arrow characters**: Spec sample uses Unicode arrows (`-->` rendered as `->`) in edge cases section ("Empty after trimming -> None", "Only special chars -> None"). Implementation uses ASCII `->` (`constants.ts:75-76`). Purely cosmetic at the rendered font size.

6. **LOW -- Wall fade timing range**: Spec says frames 270-360 for test walls appearing (spec lines 133-135). Implementation now uses frames 190-230 (`constants.ts:24-25`) to fit within the ~256-frame section allocation. Walls fade in over 40 frames vs spec's 90. The compressed timing is necessary to ensure walls are visible in the integrated section context; the standalone composition also works naturally with the earlier timing.

### Notes

- **Enhancements beyond spec**: The implementation adds several polish features not in the spec: a scroll indicator bar on the right side of the content area (`LongPrompt.tsx:119-144`), "test" labels inside each wall brick (`LongPrompt.tsx:185-193`), bold styling on header lines (`LongPrompt.tsx:98`), a narration quote caption overlay at the bottom (`LongPrompt.tsx:314-342`), and the `showTestWalls` prop for compositional flexibility. All are additive and do not alter the core visual contract.
- **Line count display**: Shown in two places -- in the file header as "N lines" text (`LongPrompt.tsx:64-66`) and as a standalone `LineCountBadge` pill positioned near the header (`LongPrompt.tsx:302-303`). The spec describes a "[50L]" badge and header display, so both are covered.
- **Font family**: `JetBrains Mono, monospace` used instead of generic `monospace` (`LongPrompt.tsx:51, 89, 189`). This is an improvement for code readability with a monospace fallback.
- **MEDIUM issue mitigation (APPLIED)**: The test walls are a critical narrative element -- the spec says "Only 2-3 amber walls on right side... Emphasizes lack of test coverage" and the visual diagram prominently shows them with an arrow noting "Only 2-3 test walls." Fix applied: option (a) -- compressed LongPrompt internal timing so all phases complete within ~256 frames. Container fade 0-60, scroll 60-180, walls 190-230, hold 240+. This preserves all other visual timings in the section unchanged.
- **Dynamic line count**: The implementation computes line count dynamically (`LongPrompt.tsx:289`) rather than hardcoding 50. The actual content is 51 lines, close enough to the spec's "~50 lines" target.

### Resolution Status: RESOLVED

Issue #1 (MEDIUM) has been fixed by compressing internal BEATS timings in `constants.ts` so all animation phases complete within the ~256 internal frames available in the section context. Test walls are now fully visible by frame 230, with a hold period before unmount at frame 256. The standalone composition continues to work correctly with an extended hold at the end.

## Re-Audit Update (2026-02-09)
- **Status**: PASS
- **Result**: Two visual renders performed within the section context. (1) At section frame 921 (internal frame ~119): parser_v1.prompt file visible with blue header showing "51 lines", content scrolled partway showing validation rules and unicode support sections, scroll indicator bar visible, line count badge ("51 lines") visible. Test walls not yet visible (WALLS_FADE_START=190, internal frame only 119). (2) At section frame 1040 (internal frame ~238): All elements fully visible -- 3 amber test walls on right with "3 tests" label, content scrolled further showing edge cases and performance sections, narration caption "With few tests, your prompt needs to specify everything." visible at bottom. This confirms the compressed BEATS timing fix is working correctly: walls appear by frame 230 and hold until unmount at ~256. All spec requirements verified including syntax highlighting (blue headers, orange bullets, gray text).

### File References

- Component: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/43-LongPrompt/LongPrompt.tsx`
- Constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/43-LongPrompt/constants.ts`
- Index: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/43-LongPrompt/index.ts`
- Section composition: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/Part4PrecisionTradeoff.tsx`
- Section constants: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/S04-PrecisionTradeoff/constants.ts`
- Root registration: `/Users/gregtanaka/Documents/pdd_cloud/pdd/demos/3blue1brown/remotion/src/remotion/Root.tsx` (lines 894-903)
