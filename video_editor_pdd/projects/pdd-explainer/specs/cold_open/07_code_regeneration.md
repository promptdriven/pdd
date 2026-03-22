[Remotion]

# Section 0.5: Code Regeneration

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:16 - 0:17

## Visual Description
The patched code from the previous scene is still on screen. Then — the entire function body selects (a highlight wash sweeps down the lines), and in one swift motion the code deletes. A brief empty beat (200ms). Then new, clean code streams in line-by-line from the top — same function signature, but the implementation is clean: consistent style, no patch comments, proper naming, elegant structure. Each line appears with a faint cyan glow (#00D9FF15) that fades after 200ms, suggesting the code is being generated, not written. In the bottom-left corner, a small terminal prompt shows `$ pdd generate` with a green checkmark appearing at the end.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E1E (VS Code dark)
- Line gutter: #2D2D2D, 48px wide

### Chart/Visual Elements
- **Selection highlight:** #264F7840 sweeping top-to-bottom across existing code
- **Clean code lines:** same syntax highlighting as previous spec, but no red comments
- **Generation glow:** per-line #00D9FF15 background highlight, fades over 200ms
- **Terminal overlay (bottom-left):** 320x40px, background #0D1117, border-radius 6px
  - Text: `$ pdd generate` in #E6EDF3, `JetBrains Mono` 12px
  - Green checkmark: #3FB950, appears after code finishes streaming

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Selection highlight sweeps down all code lines (top → bottom, 30ms per line)
2. **Frame 8-12 (0.27-0.4s):** Selected code deletes instantly — lines vanish, leaving empty editor
3. **Frame 12-15 (0.4-0.5s):** Empty beat — just the editor background and line numbers
4. **Frame 15-45 (0.5-1.5s):** Clean code streams in line-by-line from top. Each line appears with cyan glow that fades. ~2 lines per frame for rapid generation feel.
5. **Frame 45-50 (1.5-1.67s):** Terminal overlay fades in with `$ pdd generate`, green checkmark appears

### Typography
- Code: `JetBrains Mono`, 14px, line-height 1.6
- Terminal: `JetBrains Mono`, 12px, #E6EDF3

### Easing
- Selection sweep: `linear` (constant speed down lines)
- Code stream-in: `easeOutQuad` per line (each line decelerates into place)
- Glow fade: `easeOutExpo`
- Terminal fade-in: `easeOutCubic`

## Narration Sync
> "So why are we still patching?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={50}>
  <AbsoluteFill style={{ background: '#1E1E1E' }}>
    <Sequence from={0} durationInFrames={8}>
      <SelectionSweep lines={codeLines} />
    </Sequence>
    <Sequence from={8} durationInFrames={4}>
      <EmptyEditor />
    </Sequence>
    <Sequence from={15} durationInFrames={30}>
      <CodeStreamIn lines={cleanCodeLines} glowColor="#00D9FF15" linesPerFrame={2} />
    </Sequence>
    <Sequence from={45} durationInFrames={5}>
      <TerminalOverlay command="pdd generate" showCheck={true} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_regeneration",
  "language": "typescript",
  "theme": "vscode_dark",
  "patchedLineCount": 23,
  "cleanLineCount": 16,
  "generationGlow": "#00D9FF15",
  "terminalCommand": "pdd generate",
  "streamRate": "2_lines_per_frame"
}
```
