[Remotion]

# Section 0.6: Code Regeneration — Delete and Rebuild

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:14 - 0:16

## Visual Description

The dramatic payoff of the cold open. The patched function from the previous spec suddenly DELETES — all 24 lines vanish in a rapid cascade, lines dissolving from top to bottom. The IDE is momentarily empty. Then, in under a second, clean new code regenerates — flowing in from the top, line by line, at high speed. The new function is shorter (~16 lines), cleaner, with no patch comments, no workarounds, no TODOs. Pure, well-structured code.

In the bottom-right corner, a subtle terminal overlay appears: a small terminal window showing `$ pdd generate auth_handler` with a green checkmark and `✓ Generated in 0.8s`. This is the first hint of the product.

The visual metaphor is complete: the sock was thrown away and replaced. The code was thrown away and replaced. Same economics, different domain.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (dark IDE background, continuous from previous spec)
- Terminal overlay: bottom-right, 380x120px, `#161B22` with `#30363D` 1px border, rounded 8px

### Chart/Visual Elements

#### Phase 1: Code Deletion
- Each line dissolves sequentially, top to bottom
- Dissolution effect: line text shifts 4px right and fades to 0 opacity
- Deletion speed: ~1.5 frames per line (24 lines in ~36 frames / 1.2s)
- As lines delete, line numbers also fade
- A faint red flash `#FF7B72` at 0.05 background sweeps down with the deletion wave

#### Phase 2: Code Regeneration
- New code appears line by line, top to bottom
- Appearance effect: line fades in from 0 and slides 4px from left
- Generation speed: ~1 frame per line (16 lines in ~16 frames / 0.5s) — faster than deletion
- New code uses same syntax highlighting but NO patch comments
- A faint green flash `#5AAA6E` at 0.05 background sweeps down with the generation wave
- New function is visibly cleaner: fewer indentation levels, clear variable names, no workaround comments

#### Terminal Overlay
- Position: bottom-right corner, 40px from edges
- Size: 380x120px
- Background: `#161B22` at 0.9, border `#30363D` 1px, rounded 8px
- Content line 1: `$ pdd generate auth_handler` — JetBrains Mono, 11px, `#94A3B8`
- Content line 2: `✓ Generated in 0.8s` — JetBrains Mono, 11px, `#5AAA6E`
- Appears during generation phase

#### New Clean Code (16 lines)
- No `# patched`, `# workaround`, `# TODO`, or `# edge case` comments
- Cleaner structure: single try/except, clear validation flow
- Same function name (`validate_auth_token`) — it's a replacement, not a different function

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** Cursor stops blinking. Brief pause — something is about to happen.
2. **Frame 3-39 (0.1-1.3s):** Code deletion cascade. Lines dissolve top to bottom with red flash sweep. IDE empties.
3. **Frame 39-42 (1.3-1.4s):** Empty IDE. Brief pause. Just line numbers and the cursor gone.
4. **Frame 42-58 (1.4-1.9s):** New code generates rapidly, top to bottom, with green flash sweep. Terminal overlay fades in at frame 45.
5. **Frame 58-60 (1.9-2s):** Hold. Clean code sits. Terminal shows `✓ Generated in 0.8s`. The transformation is complete.

### Typography
- Code: JetBrains Mono, 14px, standard syntax colors (no amber patch comments in new code)
- Terminal text: JetBrains Mono, 11px, `#94A3B8` (command) and `#5AAA6E` (success)
- Line numbers: JetBrains Mono, 13px, `#484F58` at 0.4

### Easing
- Line deletion: `easeIn(quad)` — accelerates as it cascades down
- Line generation: `easeOut(cubic)` — starts fast, settles
- Terminal overlay fade-in: `easeOut(quad)` over 8 frames
- Red/green flash sweeps: `easeInOut(sine)` following the cascade

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_005`

- **0:14** ("Code just"): Deletion cascade begins — old patched code vanishes
- **0:15** ("got that cheap"): New clean code regenerates instantly — the point lands

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    <IDETopBar filename="auth_handler.py" />

    {/* Phase 1: Delete cascade */}
    <Sequence from={3} durationInFrames={36}>
      <CodeDeleteCascade
        lines={oldCodeLines}
        dissolveDirection="top_to_bottom"
        framesPerLine={1.5}
        shiftX={4}
        flashColor="#FF7B72"
        flashOpacity={0.05}
      />
    </Sequence>

    {/* Phase 2: Regeneration */}
    <Sequence from={42}>
      <CodeGenerateCascade
        lines={newCleanCodeLines}
        direction="top_to_bottom"
        framesPerLine={1}
        slideFromX={-4}
        flashColor="#5AAA6E"
        flashOpacity={0.05}
      />
    </Sequence>

    {/* Terminal overlay */}
    <Sequence from={45}>
      <FadeIn duration={8}>
        <TerminalOverlay
          x={1500} y={920}
          width={380} height={120}
          bgColor="#161B22"
          borderColor="#30363D"
          lines={[
            { text: '$ pdd generate auth_handler', color: '#94A3B8' },
            { text: '✓ Generated in 0.8s', color: '#5AAA6E' }
          ]}
          font="JetBrains Mono" fontSize={11}
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
  "filename": "auth_handler.py",
  "deletedLines": 24,
  "generatedLines": 16,
  "deletionDurationFrames": 36,
  "generationDurationFrames": 16,
  "terminal": {
    "command": "pdd generate auth_handler",
    "result": "Generated in 0.8s",
    "position": "bottom_right"
  },
  "theme": "dark_ide",
  "backgroundColor": "#0D1117",
  "narrationSegments": ["cold_open_005"]
}
```

---
