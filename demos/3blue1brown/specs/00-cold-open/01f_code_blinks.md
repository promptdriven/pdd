# Section 0.6: Code Blinks

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 1:25 - 1:35

## Visual Description

Return to the code side. A code editor fills the frame showing a complex function riddled with patches -- inline comments like `// patched for edge case`, diff-colored lines, and layered fixes stacked on top of each other. A cursor blinks steadily at the end of a particularly gnarly conditional block. Hold for a beat. The function is a visual embodiment of accumulated technical debt: it works, but barely, and every line carries the weight of a previous compromise.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1E1E2E)
- Full-frame code editor view (no split screen)
- Editor chrome: minimal -- gutter with line numbers, subtle scrollbar

### Animation Elements

1. **Code Editor Frame**
   - Full-screen dark code editor (VS Code / Cursor aesthetic)
   - Font: JetBrains Mono, ~16px equivalent
   - Line numbers in gutter: muted gray (#555)
   - Subtle top bar with filename: `user_parser.py`

2. **Complex Patched Function**
   - ~25-30 visible lines of a Python function
   - Multiple patch layers visible through color coding:
     - Original code: neutral gray (#C0C0C0)
     - First patch: warmer gray with slight red tint (#C4A8A0)
     - Second patch: slightly more red-shifted (#C89890)
     - Third patch: distinctly warmer (#CC8880)
   - Inline comments scattered throughout:
     - `# patched: handle None input (hotfix 2024-01)`
     - `# workaround for unicode edge case`
     - `# TODO: this whole block needs refactoring`
     - `# don't remove -- breaks downstream`
   - Nested conditionals 3-4 levels deep
   - A try/except wrapping another try/except

3. **Blinking Cursor**
   - Standard block cursor, white (#FFFFFF)
   - Blinks at ~530ms interval (standard terminal cadence)
   - Positioned at end of a complex line deep in the function
   - The cursor blink is the only motion -- everything else is static

4. **Subtle Patch Indicators**
   - Faint colored bars in the gutter (git-blame style):
     - Different muted colors for different "eras" of patches
     - 4-5 distinct color bands visible
   - Small warning icon (yellow triangle) next to one comment line

### Animation Sequence

1. **Frame 0-15 (0-0.5s):** Fade in from previous scene
   - Code editor fades in from black
   - Quick `easeOutCubic` opacity transition

2. **Frame 15-60 (0.5-2s):** Settle
   - Full code visible, viewer absorbs the complexity
   - Cursor appears and begins blinking
   - No other motion

3. **Frame 60-240 (2-8s):** Hold on patched code
   - Static hold -- the only motion is the cursor blink
   - Viewer reads the comments, absorbs the layered patches
   - The visual weight of accumulated fixes registers
   - Cursor blinks steadily: on for 16 frames, off for 16 frames

4. **Frame 240-300 (8-10s):** Final beat before transition
   - Cursor continues blinking
   - Hold for the narration to land
   - Slight vignette darkening at edges (subtle, 5% opacity)

### Code Sample

```python
def parse_user_input(raw_input, context=None, legacy=False):
    """Parse and validate user input string."""
    # patched: handle None input (hotfix 2024-01)
    if raw_input is None:
        return {"error": "null_input", "value": None}

    try:
        # workaround for unicode edge case
        if isinstance(raw_input, bytes):
            raw_input = raw_input.decode('utf-8', errors='replace')

        result = _inner_parse(raw_input)

        # don't remove -- breaks downstream
        if legacy:
            try:
                result = _apply_legacy_transform(result, context)
            except (KeyError, AttributeError):
                result["_legacy_compat"] = True

        # TODO: this whole block needs refactoring
        if context and context.get("strict_mode"):
            for key in list(result.keys()):
                if key.startswith("_"):
                    if key != "_legacy_compat":
                        del result[key]

        return result

    except UnicodeDecodeError:
        return {"error": "encoding", "raw": str(raw_input)[:50]}
    except Exception as e:  # pylint: disable=broad-except
        return {"error": "unknown", "detail": str(e)}
```

### Code Structure (Remotion)

```typescript
const CodeBlinks: React.FC = () => {
  const frame = useCurrentFrame();
  const { fps } = useVideoConfig();

  // Fade in
  const fadeIn = interpolate(
    frame,
    [0, 15],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Cursor blink: 530ms cycle (on for 265ms, off for 265ms)
  const blinkCycleFrames = Math.round(0.53 * fps);
  const cursorVisible = frame < 15
    ? false
    : Math.floor((frame - 15) / (blinkCycleFrames / 2)) % 2 === 0;

  // Subtle vignette at end
  const vignetteOpacity = interpolate(
    frame,
    [240, 300],
    [0, 0.05],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1E1E2E', opacity: fadeIn }}>
      {/* Editor chrome */}
      <EditorTopBar filename="user_parser.py" />

      {/* Line number gutter */}
      <LineNumberGutter startLine={47} lineCount={30} />

      {/* Patched code block */}
      <CodeBlock
        code={patchedFunctionCode}
        patchLayers={[
          { lines: [1, 2, 3, 4], era: 'original', color: '#C0C0C0' },
          { lines: [5, 6, 7], era: 'hotfix-2024-01', color: '#C4A8A0' },
          { lines: [10, 11, 12, 13], era: 'unicode-fix', color: '#C89890' },
          { lines: [17, 18, 19, 20, 21], era: 'refactor-todo', color: '#CC8880' },
        ]}
        comments={inlineComments}
      />

      {/* Git blame gutter colors */}
      <BlameGutter
        bands={[
          { lines: [1, 4], color: '#3A4A5A' },
          { lines: [5, 7], color: '#4A3A3A' },
          { lines: [8, 13], color: '#4A4A3A' },
          { lines: [14, 21], color: '#5A3A3A' },
          { lines: [22, 30], color: '#3A3A4A' },
        ]}
      />

      {/* Blinking cursor */}
      {cursorVisible && (
        <Cursor
          line={21}
          column={38}
          color="#FFFFFF"
        />
      )}

      {/* Warning icon */}
      <WarningIcon line={17} />

      {/* Vignette overlay */}
      <Vignette opacity={vignetteOpacity} />
    </AbsoluteFill>
  );
};
```

### Easing
- Fade-in: `easeOutCubic` over 15 frames
- Cursor blink: square wave (instant on/off), no easing
- Vignette: `linear` ramp, very subtle

## Narration Sync

> "Code just got that cheap."

The narration lands during the static hold (around frame 120-180, approximately 4-6 seconds in). The cursor continues to blink through the line -- the juxtaposition of this cheap, disposable code with the elaborate patching on screen is the point. The viewer should feel: "If code is cheap... why does this function look like an archaeological dig?"

## Audio Notes
- Ambient: very faint IDE hum / fan noise (subtle, almost subliminal)
- No keyboard sounds (nobody is typing -- the cursor just blinks)
- The silence itself is part of the beat -- a contemplative pause
- Optional: single soft, low-pitched tone as the scene fades in (transition marker)

## Visual Style Notes
- This is a "breathing room" shot -- minimal animation, maximum visual information
- The patched code should feel heavy and encrusted, like geological strata
- Color temperature: cool overall, but the patch layers introduce warmer tones (the code is aging)
- The blinking cursor is deliberately lonely -- one small point of motion in a dense, static scene
- No glow effects on the code -- code has no glow (value is not here)
- 3Blue1Brown aesthetic: clean composition despite the visual complexity of the code
- The function should be readable enough that a developer recognizes the pattern immediately

## Transition

Hard cut into Section 0.7 (01g_code_regenerates) -- the entire function deletes and regenerates clean. The contrast between this dense, patched code and the clean regeneration is the emotional payload.
