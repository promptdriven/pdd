# Section 0.7: Code Regenerates

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 1:35 - 1:50

## Visual Description

The entire patched function from the previous scene DELETES -- all lines swept away in a single, decisive motion. A brief empty beat. Then fresh, clean code regenerates line by line in under a second, filling the same space with a concise, well-structured function. No patches, no workarounds, no apologetic comments. In the bottom-right corner, a subtle terminal snippet shows `pdd generate` completing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1E1E2E)
- Full-frame code editor view (continuous from previous scene)
- Same editor chrome as 01f: gutter, line numbers, filename bar

### Animation Elements

1. **The Delete**
   - All ~30 lines of the patched function select simultaneously (brief blue highlight flash)
   - Lines dissolve/sweep upward and off-screen
   - Git-blame gutter colors vanish with the code
   - Warning icon disappears
   - Cursor disappears
   - The editor is momentarily empty (just the dark background and line numbers)

2. **The Empty Beat**
   - Blank editor with a single blinking cursor at line 47, column 1
   - Hold for ~1 second -- the emptiness is the point
   - Clean, unburdened, ready

3. **The Regeneration**
   - Fresh code types in rapidly, line by line, top to bottom
   - Each line appears with a quick left-to-right reveal (typewriter effect, but fast)
   - Total regeneration takes ~0.8 seconds (24 frames at 30fps)
   - The new function is clean, concise (~15 lines vs. the previous ~30)
   - Color: uniform neutral gray (#C0C0C0) -- no patch strata, no warm tints
   - Syntax highlighting: standard (keywords blue, strings green, comments gray)
   - No inline warning comments -- the code speaks for itself

4. **Terminal Snippet (Bottom-Right Corner)**
   - Small terminal window: ~300x120px in bottom-right corner
   - Background: slightly lighter dark (#252535) with subtle border
   - Monospace text, muted color (#888)
   - Appears just before regeneration begins
   - Content appears line by line:
     - `$ pdd generate user_parser` (white text)
     - `Generating from prompt...` (gray, appears during regeneration)
     - `Done. (0.8s)` (soft green #5AAA6E, appears when code completes)
   - The terminal is deliberately understated -- it is not the focus

5. **Post-Regeneration State**
   - Clean code fills the editor
   - No git-blame color bands (fresh generation, no history)
   - Line numbers reset to clean sequence
   - Cursor blinks at end of the new function
   - The visual relief is palpable -- less code, more clarity

### Regenerated Code Sample

```python
def parse_user_input(raw_input: str | None, context: dict | None = None) -> dict:
    """Parse and validate user input string.

    Args:
        raw_input: The raw input string to parse, or None.
        context: Optional context dictionary for strict mode filtering.

    Returns:
        Parsed result dictionary, or error dictionary on failure.
    """
    if raw_input is None:
        return {"error": "null_input", "value": None}

    text = raw_input if isinstance(raw_input, str) else raw_input.decode("utf-8", errors="replace")
    result = _inner_parse(text)

    if context and context.get("strict_mode"):
        result = {k: v for k, v in result.items() if not k.startswith("_")}

    return result
```

### Animation Sequence

1. **Frame 0-6 (0-0.2s):** Selection flash
   - All lines of the patched function highlight blue simultaneously
   - Brief flash: opacity 0 -> 0.4 -> 0 over 6 frames

2. **Frame 6-30 (0.2-1s):** Delete sweep
   - Lines dissolve upward with staggered timing
   - Top lines go first, bottom lines follow (0.5-frame stagger per line)
   - Each line: opacity fades while translating Y upward by 20px
   - Gutter colors and warning icon fade simultaneously
   - Particle-like dissolve effect on characters (optional, subtle)

3. **Frame 30-60 (1-2s):** Empty beat
   - Empty editor holds
   - Single cursor blinks at line 47
   - Terminal window fades in at bottom-right corner
   - Terminal shows: `$ pdd generate user_parser`

4. **Frame 60-66 (2-2.2s):** Terminal activity
   - Terminal shows: `Generating from prompt...`
   - Brief pause

5. **Frame 66-90 (2.2-3s):** Regeneration
   - Fresh code appears line by line, top to bottom
   - ~15 lines in 24 frames = ~1.6 frames per line
   - Each line: left-to-right character reveal with slight blur leading edge
   - All text in uniform neutral gray with standard syntax highlighting
   - No patch colors, no blame gutter marks

6. **Frame 90-96 (3-3.2s):** Terminal completion
   - Terminal shows: `Done. (0.8s)` in soft green (#5AAA6E)
   - Small checkmark appears next to the line

7. **Frame 96-450 (3.2-15s):** Hold on clean code
   - Static hold on the regenerated function
   - Cursor blinks at end of the function
   - Terminal persists subtly in corner
   - Viewer absorbs the contrast: 15 clean lines vs. the 30 patched lines from before
   - The narration lands during this hold

### Code Structure (Remotion)

```typescript
const CodeRegenerates: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Phase 1: Selection flash
  const selectionOpacity = interpolate(
    frame,
    [0, 3, 6],
    [0, 0.4, 0],
    { extrapolateRight: 'clamp' }
  );

  // Phase 2: Delete sweep (staggered per line)
  const deleteProgress = interpolate(
    frame,
    [6, 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 3: Regeneration (line-by-line reveal)
  const regenProgress = interpolate(
    frame,
    [66, 90],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Terminal fade-in
  const terminalOpacity = interpolate(
    frame,
    [30, 45],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Terminal completion
  const terminalDone = frame >= 90;

  // Cursor blink (only during empty beat and post-regen)
  const blinkCycleFrames = Math.round(0.53 * fps);
  const showCursor = (frame >= 30 && frame < 66) || frame >= 90;
  const cursorVisible = showCursor &&
    Math.floor((frame - 30) / (blinkCycleFrames / 2)) % 2 === 0;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
      {/* Editor chrome */}
      <EditorTopBar filename="user_parser.py" />
      <LineNumberGutter startLine={47} lineCount={30} />

      {/* Old code (deleting) */}
      {frame < 30 && (
        <OldPatchedCode
          selectionOpacity={selectionOpacity}
          deleteProgress={deleteProgress}
        />
      )}

      {/* Empty state cursor */}
      {frame >= 30 && frame < 66 && cursorVisible && (
        <Cursor line={47} column={1} color="#FFFFFF" />
      )}

      {/* New clean code (regenerating) */}
      {frame >= 66 && (
        <CleanCodeReveal
          code={regeneratedCode}
          progress={regenProgress}
          highlightStyle="standard" // No patch colors
        />
      )}

      {/* Post-regen cursor */}
      {frame >= 90 && cursorVisible && (
        <Cursor line={65} column={1} color="#FFFFFF" />
      )}

      {/* Terminal snippet - bottom right */}
      <div style={{
        position: 'absolute',
        bottom: 40,
        right: 40,
        opacity: terminalOpacity,
      }}>
        <TerminalSnippet
          lines={[
            { text: '$ pdd generate user_parser', color: '#E0E0E0', showAt: 30 },
            { text: 'Generating from prompt...', color: '#888', showAt: 60 },
            { text: terminalDone ? 'Done. (0.8s) \u2713' : '', color: '#5AAA6E', showAt: 90 },
          ]}
          style={{
            width: 300,
            padding: '8px 12px',
            backgroundColor: '#252535',
            borderRadius: 6,
            border: '1px solid #333',
            fontFamily: 'JetBrains Mono',
            fontSize: 12,
          }}
        />
      </div>
    </AbsoluteFill>
  );
};
```

### Easing
- Selection flash: `linear` (instant on/off feel)
- Delete sweep: `easeInQuad` (accelerates as lines vanish -- decisive, not gentle)
- Empty beat: no easing (static hold)
- Regeneration line reveal: `easeOutCubic` per line (snaps in, settles)
- Terminal fade-in: `easeOutCubic`
- Terminal text appearance: instant (no fade, mimics real terminal output)

## Narration Sync

> "So why are we still patching?"

The narration begins during the hold on the clean regenerated code (approximately frame 150-300, roughly 5-10 seconds in). The question lands while the viewer is still processing the visual contrast between the 30-line patched mess and the 15-line clean regeneration. The `pdd generate` terminal output in the corner provides the implicit answer.

## Audio Notes
- Frame 0-6: Brief digital "select" sound (subtle, like highlighting text)
- Frame 6-30: Soft whoosh/sweep as lines delete upward -- satisfying, not aggressive
- Frame 30-60: Silence during the empty beat (the absence of sound is intentional)
- Frame 60-90: Rapid soft typing/generation sound -- mechanical but clean, like a printer or teletype
- Frame 90: Soft completion chime (single note, not a full success fanfare)
- Background: very faint ambient hum continues from previous scene
- The overall audio arc: destruction -> silence -> creation -> resolution

## Visual Style Notes
- The delete should feel decisive, not violent -- this is liberation, not destruction
- The empty beat is critical -- do not rush it. The blank editor is the visual thesis: code is disposable
- The regeneration should feel effortless -- fast but not frantic
- Clean code has NO glow -- it is output, not where value resides
- The terminal in the corner is deliberately small and muted -- `pdd generate` is a tool, not the hero
- Terminal uses monospace font at smaller size than the main code, with a muted gray palette
- The contrast in line count (30 -> 15) should be visually obvious without annotation
- No git-blame gutter colors on the new code -- it has no history, no layers, no baggage
- 3Blue1Brown aesthetic: the animation communicates the idea cleanly, without excess

## PDD Command Placement

Per the PDD Commands Visual Placement table (timestamp 0:38):
- **Command:** `pdd generate`
- **Position:** Bottom-right corner terminal snippet
- **Style:** Monospace, muted (#888 on #252535 background)
- **Timing:** Appears during empty beat, completes with regeneration
- **Purpose:** Seeds the tool name without drawing focus from the visual narrative

## Transition

Crossfade into Section 0.8 (01h_title_card) -- the title "Prompt-Driven Development" fades in over the clean regenerated code. The code remains visible but dims slightly as the title takes visual priority.
