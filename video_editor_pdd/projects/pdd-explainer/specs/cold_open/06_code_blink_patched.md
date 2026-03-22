[Remotion]

# Section 0.4: Code Blink — Delete and Regenerate

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description

Return to the code side. A complex function full of patches is visible on a dark IDE background — the same code we saw in the zoom-out, but now filling the full frame (no split). The cursor blinks on a particularly gnarly function with visible `// patched`, `// workaround`, and `// TODO: refactor` comments.

Then the entire function DELETES — lines dissolve from top to bottom in a smooth wipe, leaving empty space. A beat of emptiness. Then new code regenerates from nothing: clean, well-structured lines appear from top to bottom, filling the same space but with none of the cruft. The regenerated code is visibly cleaner — consistent naming, no hack comments, proper structure.

In the bottom-right corner, a subtle terminal snippet shows `pdd generate` completing with a green checkmark.

This is the visual thesis of the entire video compressed into 2 seconds.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (dark IDE background)
- No split — full frame code view

### Chart/Visual Elements

#### Old Code Block (pre-delete)
- Font: JetBrains Mono, 13px, line-height 20px
- Code area: x: 80, y: 120, width: 1760, height: 840
- Line numbers: JetBrains Mono, 13px, `#4A5568` at 0.3, x: 40
- Code coloring (syntax highlighting):
  - Keywords (`function`, `return`, `if`): `#C792EA` (purple)
  - Strings: `#C3E88D` (green)
  - Variables: `#82AAFF` (blue)
  - Comments: `#546E7A` (muted gray-green)
- Hack comment highlights:
  - `// patched` — `#D9944A` at 0.15 background
  - `// workaround` — `#D9944A` at 0.12 background
  - `// TODO: refactor` — `#E74C3C` at 0.1 background
- ~25 lines of complex, patch-heavy code
- Cursor: blinking `|` at line 1, `#E2E8F0` at 0.8, 500ms blink cycle

#### Delete Animation
- Lines dissolve top-to-bottom, each line fading to 0 opacity over 3 frames
- Staggered: 1-frame delay between each line
- Dissolve color: brief flash of `#D9944A` at 0.1 as each line vanishes
- Total delete: ~25 lines × 1 frame delay = 25 frames (~0.83s)

#### Regenerated Code Block (post-generate)
- Same font and positioning as old code
- Clean code — no hack comments, consistent style
- Lines appear top-to-bottom, fading from 0 to full opacity over 3 frames
- Staggered: 1-frame delay between each line
- Appear color: brief flash of `#4A90D9` at 0.08 as each line materializes
- Total regeneration: ~25 lines × 1 frame delay = 25 frames (~0.83s)

#### Terminal Snippet (corner)
- Position: bottom-right, x: 1500, y: 980
- Background: `#1A1B26` rounded rect with `#334155` 1px border at 0.2
- Text: `$ pdd generate ✓` — JetBrains Mono, 10px
  - `$`: `#5AAA6E` at 0.4
  - `pdd generate`: `#E2E8F0` at 0.5
  - `✓`: `#5AAA6E` at 0.7
- Fades in at frame 50 (during regeneration)

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Old code visible, cursor blinking. The function is ugly — comments, hacks, patches.
2. **Frame 8-33 (0.27-1.1s):** Delete wipe — lines dissolve top-to-bottom with amber flash. Each line takes 3 frames to fade, staggered 1 frame apart.
3. **Frame 33-35 (1.1-1.17s):** Empty space. Brief pause. Just the dark background and line numbers.
4. **Frame 35-60 (1.17-2s):** Regeneration — clean new lines appear top-to-bottom with blue flash. Terminal snippet fades in at frame 50.

### Typography
- Code: JetBrains Mono, 13px, syntax-highlighted
- Line numbers: JetBrains Mono, 13px, `#4A5568` at 0.3
- Terminal: JetBrains Mono, 10px

### Easing
- Line dissolve: `easeOut(quad)` per line, 3 frames
- Line appear: `easeOut(quad)` per line, 3 frames
- Terminal fade-in: `easeOut(quad)` over 8 frames

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_005`

- **14.12s** ("Code"): Old patched code visible, delete begins
- **15.00s** ("just got that cheap"): Regeneration in progress — clean code appearing
- **15.86s**: Terminal `pdd generate ✓` visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Old code — visible then deletes */}
    <CodeBlock
      code={OLD_PATCHED_CODE}
      font="JetBrains Mono" size={13}
      x={80} y={120}
      lineNumbers
      highlights={[
        { line: 3, comment: '// patched', color: '#D9944A' },
        { line: 11, comment: '// workaround', color: '#D9944A' },
        { line: 18, comment: '// TODO: refactor', color: '#E74C3C' },
      ]}
      deleteAt={8}
      deleteDuration={25}
      deleteColor="#D9944A"
    />

    {/* Regenerated code — appears after delete */}
    <Sequence from={35}>
      <CodeBlock
        code={CLEAN_REGENERATED_CODE}
        font="JetBrains Mono" size={13}
        x={80} y={120}
        lineNumbers
        appearDuration={25}
        appearColor="#4A90D9"
      />
    </Sequence>

    {/* Terminal snippet */}
    <Sequence from={50}>
      <FadeIn duration={8}>
        <TerminalSnippet
          command="pdd generate"
          status="success"
          x={1500} y={980}
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_animation",
  "animation": "delete_and_regenerate",
  "oldCode": {
    "lines": 25,
    "hackComments": ["// patched", "// workaround", "// TODO: refactor"],
    "style": "complex_patched_function"
  },
  "newCode": {
    "lines": 25,
    "style": "clean_regenerated",
    "noHackComments": true
  },
  "deleteAnimation": {
    "direction": "top_to_bottom",
    "flashColor": "#D9944A",
    "stagger": "1_frame"
  },
  "regenerateAnimation": {
    "direction": "top_to_bottom",
    "flashColor": "#4A90D9",
    "stagger": "1_frame"
  },
  "terminalSnippet": {
    "command": "pdd generate",
    "status": "success",
    "checkColor": "#5AAA6E"
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_005"]
}
```

---
