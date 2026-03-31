[Remotion]

# Section 0.6: Code Regeneration — The Delete and Rebuild

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:26 - 0:31

## Visual Description

The dramatic payoff. The same code editor from spec 05, still showing the patched `process_order()` function. Then — the entire function selects (blue highlight sweeps down all 40 lines) and DELETES. A beat of empty space. Then clean, fresh code regenerates line by line, flowing onto the screen. The new function is shorter (~25 lines), clean, with zero patch comments. No HACK, no TODO, no workaround. In the bottom-right corner, a subtle terminal overlay shows `$ pdd generate process_order` completing with a green checkmark.

This is the "wow" moment — the visual thesis statement of PDD. Code is disposable. Regenerate, don't repair.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#1E1E2E` (VS Code dark theme, continuing from spec 05)
- Gutter: `#2D2D3D`, 60px wide

### Chart/Visual Elements

#### Selection Highlight
- Color: `#89B4FA` at 0.2 opacity (blue selection)
- Sweeps top-to-bottom across all 40 lines

#### Deletion Effect
- All selected lines collapse upward simultaneously
- Brief flash of empty editor — just line numbers and background

#### Regenerated Code
- Clean `process_order()` function, ~25 lines
- No patch comments, no HACKs, no TODOs
- Same syntax colors as spec 05 but the code is clearly simpler and better structured
- Lines appear with a typewriter effect, ~3 lines per second

#### Terminal Overlay
- Position: Bottom-right corner, 400x80px
- Background: `#11111B` at 0.9 opacity, 8px border-radius
- Font: JetBrains Mono, 12px
- Content: `$ pdd generate process_order ✓` in `#A6E3A1` (green)
- Appears after code regeneration completes

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Continuing from spec 05. Patched code visible at 0.85 opacity.
2. **Frame 5-25 (0.17-0.83s):** Blue selection highlight sweeps down all 40 lines, top to bottom.
3. **Frame 25-35 (0.83-1.17s):** All selected code DELETES simultaneously. Lines collapse. Brief beat — empty editor.
4. **Frame 35-45 (1.17-1.5s):** Empty editor holds. Just line numbers, background, cursor blinking on line 1. The silence is intentional.
5. **Frame 45-120 (1.5-4s):** New code regenerates. Lines flow in from the cursor position, typewriter-style, ~3 lines per second. Clean, fresh, no patches. Syntax highlighting applies as each line appears.
6. **Frame 120-135 (4-4.5s):** Terminal overlay fades in at bottom-right: `$ pdd generate process_order ✓`
7. **Frame 135-150 (4.5-5s):** Hold on clean code + terminal. Everything is fresh and simple.

### Typography
- Code: JetBrains Mono, 14px, syntax colors (same as spec 05)
- Terminal overlay: JetBrains Mono, 12px, `#A6E3A1`

### Easing
- Selection sweep: `linear` over 20 frames (fast, decisive)
- Deletion collapse: `easeIn(cubic)` over 10 frames
- Empty editor hold: static, 10 frames
- Code regeneration: `linear` typewriter, 3 lines/sec
- Terminal fade-in: `easeOut(quad)` over 15 frames

## Narration Sync
> "watch this. It takes..."
> "15 lines of prompt, and the code regenerates."

Segments: `cold_open_007`, `cold_open_008` (partial)

- **26.32s** (seg 007): "watch this" — selection begins sweeping
- **27.00s**: Code deletes, empty beat
- **27.56s** (seg 007 ends / seg 008 begins): "15 lines of prompt" — regeneration begins
- **31.00s**: Code flowing in, terminal overlay appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  {/* Editor chrome persists from spec 05 */}
  <CodeEditorChrome filename="process_order.py" theme="catppuccin-mocha" />

  {/* Old patched code — visible briefly */}
  <Sequence from={0} durationInFrames={25}>
    <CodeBlock
      code={PROCESS_ORDER_PATCHED}
      language="python"
      opacity={0.85}
    />
  </Sequence>

  {/* Selection sweep */}
  <Sequence from={5} durationInFrames={20}>
    <SelectionHighlight
      startLine={1} endLine={40}
      color="#89B4FA" opacity={0.2}
      sweepDuration={20}
    />
  </Sequence>

  {/* Delete animation */}
  <Sequence from={25} durationInFrames={10}>
    <CodeDelete lines={40} easing="easeInCubic" />
  </Sequence>

  {/* Empty beat */}
  <Sequence from={35} durationInFrames={10}>
    <EmptyEditor lineNumbers={true} />
  </Sequence>

  {/* Regeneration */}
  <Sequence from={45} durationInFrames={75}>
    <CodeTypewriter
      code={PROCESS_ORDER_CLEAN}
      language="python"
      linesPerSecond={3}
    />
  </Sequence>

  {/* Terminal overlay */}
  <Sequence from={120} durationInFrames={30}>
    <FadeIn durationFrames={15}>
      <TerminalOverlay
        command="pdd generate process_order"
        status="success"
        position="bottom-right"
      />
    </FadeIn>
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "code_regeneration",
  "durationFrames": 150,
  "fps": 30,
  "narrationSegments": ["cold_open_007", "cold_open_008"],
  "codeFile": "process_order.py",
  "deletedLines": 40,
  "regeneratedLines": 25,
  "pddCommand": "pdd generate process_order"
}
```

---
