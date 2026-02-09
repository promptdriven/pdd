# Audit: 01g_code_regenerates.md

## Spec Summary
Code deletion and regeneration sequence (~15 seconds, 1:35-1:50):
- Patched function from 01f deletes (blue selection flash, lines sweep upward)
- Empty editor with blinking cursor hold (~1 second)
- Fresh clean code regenerates line-by-line in ~0.8 seconds
- Terminal snippet in bottom-right shows `pdd generate user_parser` with completion message
- Final hold on clean regenerated code
- Narration: "So why are we still patching?" lands during hold on clean code
- Crossfade transition to 01h title card

## Implementation Status
Partially Implemented

## Deltas Found

### Delta 1: Combined with 01f into single sequence
- **Spec says**: This is Section 0.7 starting at 1:35, following the separate 01f "Code Blinks" section at 1:25-1:35
- **Implementation does**: ColdOpenSection.tsx VISUAL_03 (lines 73-115) combines both 01f and 01g into one sequence running 12.78-13.76s (383-413 frames = 1 second duration). Old code blurs out, new code fades in
- **Severity**: High - Timeline completely different, merged implementation

### Delta 2: No deletion animation with selection flash
- **Spec says**: "Frame 0-6 (0-0.2s): Selection flash - All lines highlight blue simultaneously, Brief flash: opacity 0 → 0.4 → 0 over 6 frames. Frame 6-30 (0.2-1s): Delete sweep - Lines dissolve upward with staggered timing, top lines go first, particle-like dissolve effect"
- **Implementation does**: Old code simply blurs out with opacity fade (line 82-83), no selection flash, no upward sweep animation, no staggered line-by-line deletion
- **Severity**: Medium - Different visual effect, less dramatic

### Delta 3: No empty editor hold
- **Spec says**: "Frame 30-60 (1-2s): Empty beat - Empty editor holds, Single cursor blinks at line 47, Terminal window fades in at bottom-right corner. The emptiness is the point"
- **Implementation does**: Direct crossfade from old to new code, no empty state, no pause, no blinking cursor moment
- **Severity**: High - Key conceptual beat missing ("code is disposable")

### Delta 4: No line-by-line regeneration animation
- **Spec says**: "Frame 66-90 (2.2-3s): Regeneration - Fresh code appears line by line, top to bottom, ~15 lines in 24 frames = ~1.6 frames per line, Each line: left-to-right character reveal with slight blur leading edge"
- **Implementation does**: New code fades in as a complete block (lines 90-100), no typewriter effect, no line-by-line reveal, instant appearance
- **Severity**: High - "Effortless generation" effect completely missing

### Delta 5: Terminal implementation differs
- **Spec says**: "Terminal Snippet (Bottom-Right Corner) - Small terminal window: ~300x120px, Background: slightly lighter dark (#252535) with subtle border, Content appears line by line as generation progresses, Shows completion time and checkmark"
- **Implementation does**: Terminal text appears at bottom-right (lines 102-112) but only shows final command `$ pdd generate user_parser`, no multi-line progression, no "Generating from prompt...", no "Done. (0.8s) ✓" with timing and checkmark
- **Severity**: Medium - Simplified terminal output loses the sense of process

### Delta 6: No git-blame gutter removal
- **Spec says**: "No git-blame gutter colors on the new code -- it has no history, no layers, no baggage" - emphasizing the fresh start
- **Implementation does**: No git-blame gutters shown in either old or new code (both are plain pre blocks), so this contrast doesn't exist
- **Severity**: Low - Related to missing 01f implementation

### Delta 7: Code samples differ slightly
- **Spec says**: Regenerated code shows clean 15-line function with type hints `def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:` and dictionary comprehension
- **Implementation does**: Regenerated code (lines 98) is similar spirit but slightly different implementation (6 lines vs 15), uses simpler approach without explicit type hints or dict comprehension
- **Severity**: Low - Both show the concept of "less code, more clarity"

### Delta 8: Timing is drastically compressed
- **Spec says**: 15-second sequence with distinct phases: deletion (1s), empty hold (1s), regeneration (0.8s), then 11+ seconds holding on clean code
- **Implementation does**: Entire VISUAL_03 is 1 second (383-413 frames at 30fps), then immediately transitions to VISUAL_04 title card
- **Severity**: High - Spec's deliberate pacing completely changed

### Delta 9: No audio cues specified in implementation
- **Spec says**: "Brief digital 'select' sound (subtle), Soft whoosh/sweep as lines delete, Silence during empty beat, Rapid soft typing/generation sound, Soft completion chime"
- **Implementation does**: Only references cold_open_narration.wav (line 29), no sound effects visible in code
- **Severity**: Medium - Audio design not implemented (or implemented separately)

### Delta 10: Transition to title card different
- **Spec says**: "Crossfade into Section 0.8 (01h_title_card) -- the title 'Prompt-Driven Development' fades in over the clean regenerated code. The code remains visible but dims slightly"
- **Implementation does**: VISUAL_03 ends at frame 413, VISUAL_04 (title card) starts at frame 423 - a 10-frame gap with hard cut, not a crossfade. Code does dim in background (line 127 opacity 0.25) but transition is different
- **Severity**: Medium - Transition style differs

## Missing Elements

1. **Deletion animation components**: No OldPatchedCode component with selection flash and staggered line-by-line upward sweep as described in spec's code structure (lines 182-187)

2. **Empty state with cursor**: No empty editor hold showing single blinking cursor at line 47, column 1 (spec lines 190-193)

3. **Line-by-line reveal component**: No CleanCodeReveal component that types in code line-by-line with left-to-right character reveal (spec lines 196-201)

4. **Multi-stage terminal animation**: No TerminalSnippet component showing command → "Generating..." → "Done ✓" progression (spec lines 213-230)

5. **Post-regeneration cursor**: No cursor blinking at end of regenerated function during the hold (spec lines 203-207)

6. **Visual relief emphasis**: Spec emphasizes "The contrast in line count (30 → 15) should be visually obvious without annotation" but current implementation shows similar-sized code blocks

7. **Easing variations**: Spec details specific easing for each phase (easeInQuad for deletion, easeOutCubic for regeneration, etc.) - not implemented in current simple fade transitions

## Notes

This spec describes a deliberate, almost ceremonial process: code is selected, swept away, the editor sits empty (emphasizing disposability), then new code generates with visible process, culminating in a long contemplative hold. The philosophical point is that code regeneration should feel "decisive, not violent" and "effortless -- fast but not frantic."

The implementation condenses this 15-second philosophical journey into a 1-second fade transition, losing the narrative beats entirely. The terminal command appears but doesn't show the generation process. The empty editor beat - which the spec calls "critical -- do not rush it" - is completely absent.

This suggests significant scope reduction from spec to implementation, possibly due to:
1. Time constraints (cold open needed to be shorter)
2. Pacing feedback (the deliberate beats felt too slow)
3. Technical complexity (line-by-line animations are more complex than fades)

The current implementation communicates "old code becomes new code" but not the spec's intended message about code being disposable/regenerable through an AI tool.

## Resolution Status
- **Status**: NOT RESOLVED (Veo video implementation path)
- **Changes Made**: None - this segment is part of the Veo video implementation in ColdOpenSection.tsx, not the Remotion fallback.
- **Remaining Issues**:
  - The Remotion fallback implementation (01-ColdOpen components) does not include this beat as a separate composition
  - ColdOpenSection.tsx uses Veo video files which may or may not include this code regeneration sequence as specified
  - To implement this in Remotion fallback would require:
    - Creating a new CodeRegenerates.tsx component
    - Deletion animation with selection flash and upward sweep
    - Empty editor state with blinking cursor
    - Line-by-line code regeneration with typewriter effect
    - Multi-stage terminal animation showing generation process
    - Integration into the sequence after split-screen
  - This is beyond the scope of fixing the existing 01-ColdOpen Remotion implementation, which focuses on the split-screen sequence only
  - The philosophical beats (emptiness, disposability, effortless regeneration) are better suited to the Veo video implementation path
