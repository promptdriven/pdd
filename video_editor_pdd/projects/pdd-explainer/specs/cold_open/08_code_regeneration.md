[Remotion]

# Section 0.8: Code Regeneration — Delete and Rebuild

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:16 - 0:18

## Visual Description
The dramatic payoff of the cold open. The same patched function from the previous shot is visible. Then — the entire function selects (highlight sweeps from top to bottom), and DELETES in one swift motion. The screen is momentarily empty (just the function signature and empty body). Then new code FLOWS in — line by line, fast, clean, no patch comments, no TODO markers. The regenerated function is shorter (30 lines vs. 40), cleaner, and clearly better structured. In the bottom-right corner, a subtle terminal overlay shows `$ pdd generate process_order` completing with a green checkmark. The message is visceral: why patch when you can regenerate?

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#1E1E2E` (VS Code dark theme background)
- Editor chrome: Same as previous shot — continuous visual flow

### Chart/Visual Elements

#### Code Editor (inherited state)
- Starts showing the same patched function from 07_code_cursor_blink
- Same line numbers, same syntax highlighting, same patch comments

#### Selection Highlight
- Full-function selection: `#89B4FA` at 0.2 (blue selection)
- Sweeps from line 1 to line 40 in 8 frames

#### Regenerated Code
- Clean function: ~30 lines, no comments, clear variable names
- Standard Python syntax highlighting (Catppuccin Mocha)
- Lines appear top-to-bottom, 1 line per frame

#### Terminal Overlay
- Position: Bottom-right, 400x60px
- Background: `#11111B` at 0.9, 8px border-radius
- Text: `$ pdd generate process_order ✓` in `#A6E3A1` (green)
- Font: JetBrains Mono, 12px

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Selection highlight sweeps across the entire function (lines 1-40). Blue selection overlay appears line by line, 5 lines per frame.
2. **Frame 8-12 (0.27-0.4s):** All selected code DELETES. Lines vanish simultaneously. Only the function signature remains: `def process_order(order, ctx):` with an empty body.
3. **Frame 12-14 (0.4-0.47s):** Brief pause. Empty function body. The "void" beat.
4. **Frame 14-44 (0.47-1.47s):** New code flows in, one line per frame. Clean, well-structured, no patch comments. 30 lines of regenerated code appear rapidly.
5. **Frame 38-48 (1.27-1.6s):** Terminal overlay fades in at bottom-right showing `$ pdd generate process_order ✓`.
6. **Frame 48-60 (1.6-2.0s):** Hold. Clean code visible. Terminal checkmark glows. The transformation is complete.

### Typography
- Code: JetBrains Mono, 14px, Catppuccin Mocha syntax colors
- Terminal: JetBrains Mono, 12px, `#A6E3A1` on `#11111B`

### Easing
- Selection sweep: `linear` (mechanical, deliberate)
- Code delete: `easeIn(quad)` — accelerates into deletion
- Void pause: static (2 frames)
- Code flow-in: `easeOut(cubic)` per line (each line decelerates as it settles)
- Terminal fade-in: `easeOut(quad)` over 10 frames
- Checkmark appear: `spring(stiffness: 200, damping: 15)`

## Narration Sync
> "So why are we still patching?"

Segment: `cold_open_006`

- **16.04s**: Function selects and deletes
- **16.5s**: Regeneration begins — clean code flows in
- **17.4s**: Terminal shows `pdd generate` completing
- **17.90s**: Hold on clean regenerated code, transition to title card

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    {/* Patched code (inherited from previous shot) */}
    <CodeEditor
      language="python"
      theme="catppuccin-mocha"
      code={PATCHED_FUNCTION_CODE}
    />

    {/* Selection sweep */}
    <Sequence from={0} durationInFrames={8}>
      <SelectionHighlight
        startLine={1} endLine={40}
        color="#89B4FA" opacity={0.2}
        sweepFrames={8}
      />
    </Sequence>

    {/* Delete + regenerate */}
    <Sequence from={8}>
      <CodeDelete duration={4} />
    </Sequence>

    <Sequence from={14}>
      <CodeFlowIn
        code={CLEAN_FUNCTION_CODE}
        linesPerFrame={1}
        easing="easeOutCubic"
      />
    </Sequence>

    {/* Terminal overlay */}
    <Sequence from={38}>
      <FadeIn duration={10}>
        <TerminalOverlay
          command="pdd generate process_order"
          status="success"
          position="bottom-right"
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_regeneration",
  "language": "python",
  "theme": "catppuccin-mocha",
  "functionName": "process_order",
  "originalLines": 40,
  "regeneratedLines": 30,
  "patchCommentsRemoved": 6,
  "terminalCommand": "pdd generate process_order",
  "phases": [
    { "name": "select", "startFrame": 0, "endFrame": 8 },
    { "name": "delete", "startFrame": 8, "endFrame": 12 },
    { "name": "void", "startFrame": 12, "endFrame": 14 },
    { "name": "regenerate", "startFrame": 14, "endFrame": 44 },
    { "name": "terminal", "startFrame": 38, "endFrame": 48 },
    { "name": "hold", "startFrame": 48, "endFrame": 60 }
  ],
  "narrationSegments": ["cold_open_006"],
  "durationSeconds": 2.0
}
```

---
