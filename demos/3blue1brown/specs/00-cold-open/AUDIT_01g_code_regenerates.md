# Audit: 01g_code_regenerates.md

## Status: ISSUES FOUND

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
Three relevant implementations exist:
1. **S00-ColdOpen/ColdOpenSection.tsx** (VISUAL_03, lines 72-115): The primary section-level composition that sequences all cold open beats. Contains the code regeneration beat as an inline Remotion composition using Veo-style timing.
2. **01-ColdOpen/**: The Remotion fallback split-screen composition (ColdOpenSplitScreen.tsx, LeftPanel.tsx, RightPanel.tsx). Does NOT contain a code regeneration beat at all -- it covers the split-screen compare/zoom-out only.
3. **27-CodeRegenerates/CodeRegenerates.tsx**: A standalone composition for a later section (mold/injection metaphor). Uses `pdd fix` (not `pdd generate`), has mold cavity, test walls, and fluid simulation. This is a conceptually different composition, not an implementation of this spec.

The primary implementation for this audit is **S00-ColdOpen/ColdOpenSection.tsx** VISUAL_03.

### Requirements Met

1. **Dark background (#1E1E2E)**: ColdOpenSection.tsx VISUAL_03 uses `backgroundColor: "#1a1a2e"` on the outer fill (line 75) and `#1E1E2E` on the code panels (lines 85, 97). Close match.
2. **Old patched code shown**: Lines 77-88 display old patched code in a styled `<pre>` block with red border (`#E74C3C`), showing a multi-line patched function with inline comments like `# patched: handle None input (hotfix 2024-01)` and `# TODO: this whole block needs refactoring`.
3. **New clean code shown**: Lines 90-100 display new clean code in a `<pre>` block with neutral border (`#333`), showing a shorter function without patches or workaround comments.
4. **Terminal indicator in bottom-right**: Lines 101-112 show `$ pdd generate user_parser` positioned at `bottom: 60, right: 60` in JetBrains Mono at 12px font size. Matches spec's placement and `pdd generate` command.
5. **Old code is longer than new code**: Old code has ~14 lines with patches/comments, new code has ~7 lines. Communicates the "less code, more clarity" contrast, though not the spec's exact 30-to-15 ratio.
6. **Code font**: Both code blocks use `JetBrains Mono, monospace` at 14px (lines 86, 98).
7. **Subsequent title card**: VISUAL_04 (lines 117-157) shows "Prompt-Driven Development" title fading in over dimmed regenerated code (opacity 0.25), matching the spec's intent of title appearing over the clean code.

### Issues Found

#### Issue 1: No deletion animation (selection flash + upward sweep)
- **Spec says**: Frame 0-6: all lines highlight blue simultaneously (opacity 0 to 0.4 to 0 over 6 frames). Frame 6-30: lines dissolve upward with staggered timing, top lines go first (0.5-frame stagger), each line fades while translating Y upward by 20px. Git-blame gutter colors and warning icon disappear. Easing: `easeInQuad`.
- **Implementation does**: Old code blurs out (`filter: blur`) and fades opacity from 1 to 0 over frames 10-25 relative to VISUAL_03_START (lines 82-83). No selection flash, no staggered line-by-line deletion, no upward sweep, no particle dissolve.
- **Severity**: High

#### Issue 2: No empty editor hold ("the emptiness is the point")
- **Spec says**: Frame 30-60 (1-2s): blank editor with single blinking cursor at line 47, column 1. Hold for ~1 second. "The empty beat is critical -- do not rush it."
- **Implementation does**: Old code fades out (frames 10-25) and new code fades in (frames 18-30), overlapping. There is no moment where the editor is empty. The crossfade is direct and continuous.
- **Severity**: High -- the spec calls this the "visual thesis: code is disposable"

#### Issue 3: No line-by-line code regeneration animation
- **Spec says**: Frame 66-90 (2.2-3s): fresh code types in line by line, top to bottom. Each line has a left-to-right character reveal with slight blur leading edge. ~15 lines in 24 frames (~1.6 frames per line). Easing: `easeOutCubic` per line.
- **Implementation does**: New code fades in as a complete block (opacity 0 to 1 over frames 18-30, line 95). No typewriter effect, no sequential line reveal.
- **Severity**: High

#### Issue 4: Terminal lacks multi-stage progression
- **Spec says**: Terminal content appears in stages: (1) `$ pdd generate user_parser` in white at frame 30, (2) `Generating from prompt...` in gray (#888) at frame 60, (3) `Done. (0.8s) checkmark` in soft green (#5AAA6E) at frame 90. Terminal window has background #252535, subtle border, 300x120px, monospace at smaller size.
- **Implementation does**: Terminal shows only the single line `$ pdd generate user_parser` in #E0E0E0, fading in at frames 25-35 (lines 102-112). No background panel, no border, no "Generating from prompt..." line, no "Done. (0.8s)" completion indicator, no checkmark.
- **Severity**: Medium

#### Issue 5: Timing drastically compressed
- **Spec says**: ~15-second sequence: deletion (1s), empty hold (1s), terminal activity (0.2s), regeneration (0.8s), terminal completion (0.2s), hold on clean code (11.8s). Narration "So why are we still patching?" lands during the long hold (~frame 150-300).
- **Implementation does**: VISUAL_03 runs from frame 383 to 413 (1 second total at 30fps). Old code fades out in 0.5s, new code fades in in 0.4s, terminal fades in in 0.3s. VISUAL_04 starts at frame 423 (0.33s gap). The narration "So why are we still patching?" is mapped to VISUAL_04, not VISUAL_03.
- **Severity**: High

#### Issue 6: No editor chrome (gutter, line numbers, filename bar)
- **Spec says**: "Full-frame code editor view (continuous from previous scene). Same editor chrome as 01f: gutter, line numbers, filename bar." Spec references `EditorTopBar filename="user_parser.py"` and `LineNumberGutter startLine={47} lineCount={30}`.
- **Implementation does**: Code is shown in styled `<div>` and `<pre>` blocks with no editor chrome. No line numbers, no gutter, no filename bar. Old code panel has a red border, new code panel has a gray border.
- **Severity**: Medium

#### Issue 7: No blinking cursor
- **Spec says**: Cursor blinks at line 47, column 1 during empty beat (frame 30-66), then at end of regenerated function during hold (frame 90+). Blink cycle is ~0.53s.
- **Implementation does**: No cursor element at all.
- **Severity**: Medium

#### Issue 8: Code samples differ from spec
- **Spec says**: Regenerated code is exactly `def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:` with type hints, docstring, dictionary comprehension, and `_inner_parse` call (~15 lines).
- **Implementation does**: Regenerated code is `def parse_user_input(raw_input, context=None):` without type hints, no docstring, no dictionary comprehension (~7 lines). Old code has ~14 lines vs spec's ~30.
- **Severity**: Low -- concept of "less code, more clarity" is preserved

#### Issue 9: No git-blame gutter contrast
- **Spec says**: Old code has git-blame gutter colors (showing patch history), new code has NO git-blame colors (fresh generation, no history). The contrast emphasizes the "no baggage" aspect.
- **Implementation does**: Neither old nor new code has git-blame gutters. Old code has a red border to signal "bad" and inline comments signal patches, but the gutter-based visual storytelling is absent.
- **Severity**: Low -- related to missing editor chrome (Issue 6)

#### Issue 10: Transition to title card is not a crossfade
- **Spec says**: "Crossfade into Section 0.8 (01h_title_card) -- the title 'Prompt-Driven Development' fades in over the clean regenerated code. The code remains visible but dims slightly as the title takes visual priority."
- **Implementation does**: VISUAL_03 ends at frame 413, VISUAL_04 starts at frame 423 (10-frame gap = 0.33s of no visual). VISUAL_04 does show dimmed code (opacity 0.25) in the background with the title fading in, but the transition between visuals is a hard cut, not a crossfade overlay.
- **Severity**: Medium

#### Issue 11: No audio cues
- **Spec says**: Detailed audio design: digital "select" sound, whoosh/sweep during deletion, silence during empty beat, typing/generation sound during regeneration, soft completion chime. "The overall audio arc: destruction -> silence -> creation -> resolution."
- **Implementation does**: Only `cold_open_narration.wav` audio (line 29). No sound effect tracks visible in the code.
- **Severity**: Medium -- may be handled externally in post-production

#### Issue 12: Background color mismatch
- **Spec says**: Background `#1E1E2E` (dark navy).
- **Implementation does**: Outer AbsoluteFill uses `#1a1a2e` (line 75), code panels use `#1E1E2E` (lines 85, 97). The 6-unit difference in the red channel creates a visible two-tone effect rather than the spec's single-tone editor view.
- **Severity**: Low

### Notes

The spec describes this as a pivotal narrative moment with five distinct phases: selection flash, decisive deletion, contemplative empty beat, effortless regeneration, and long contemplative hold. The spec explicitly marks the empty editor beat as "critical -- do not rush it" since it communicates the thesis that code is disposable.

The S00-ColdOpen implementation compresses this entire 15-second sequence into a 1-second crossfade between old and new code blocks. This is a substantial scope reduction that loses all of the spec's distinct animation phases and the key narrative beat (emptiness). The terminal is reduced from a multi-stage indicator to a single static line.

The standalone `27-CodeRegenerates` composition in the codebase is for a different conceptual scene (mold/injection metaphor at a later point in the video) and uses `pdd fix` rather than `pdd generate`. It is not an implementation of this cold open spec, though it shares thematic DNA (old code dissolves, new code appears, terminal shows process).

The `01-ColdOpen/` Remotion fallback directory does not contain any code regeneration beat at all -- it only covers the split-screen comparison of developer and grandmother.

There is no dedicated Remotion composition in either the S00-ColdOpen or 01-ColdOpen directories that implements the spec's detailed animation sequence (selection flash, staggered deletion, empty beat, typewriter regeneration, multi-stage terminal). To reach spec compliance, a new dedicated component would need to be built and integrated into the ColdOpenSection visual sequence with significantly expanded timing.
