[Remotion]

# Section 7.3: PDD Bug-Fix Terminal — `pdd bug → pdd fix → ✓`

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:03 - 0:08

## Visual Description
A clean, minimal terminal overlay animates in the lower-right of the screen (or center, composited after the developer veo clip fades). The terminal shows three sequential commands executing one after another, each completing with a satisfying result:

1. `$ pdd bug email_validator` → outputs "Test added: test_rejects_unicode_homoglyphs"
2. `$ pdd fix email_validator` → outputs "Regenerating... ✓ All tests pass"
3. A final green checkmark pulses once

The terminal styling is dark with monospace text, subtle and professional — never the hero element, always a supporting detail.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black) — or composited over veo clip
- Terminal panel: `#111827` with `1px` border `#1E293B`, rounded corners `8px`

### Chart/Visual Elements

#### Terminal Panel
- Position: centered, `(360, 300)` to `(1560, 780)`
- Width: `1200px`, height: `480px`
- Background: `#111827`
- Border: `1px solid #1E293B`, radius `8px`
- Top bar: simulated macOS dots (`#EF4444`, `#F59E0B`, `#22C55E` at 8px diameter)

#### Command Lines
| Line | Text | Color | Y-offset |
|------|------|-------|----------|
| 1 | `$ pdd bug email_validator` | `#22C55E` (prompt) + `#E2E8F0` (command) | 380 |
| 2 | `  Test added: test_rejects_unicode_homoglyphs` | `#94A3B8` | 420 |
| 3 | `$ pdd fix email_validator` | `#22C55E` + `#E2E8F0` | 480 |
| 4 | `  Regenerating... ✓ All tests pass` | `#22C55E` | 520 |

#### Green Checkmark
- Large `✓` character, `#22C55E`, 48px, centered at `(960, 640)`
- Pulse scale: `1.0→1.15→1.0`

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Terminal panel fades in.
2. **Frame 15-45 (0.5-1.5s):** Line 1 types out character by character. Line 2 appears after a brief delay.
3. **Frame 45-75 (1.5-2.5s):** Line 3 types out. Line 4 appears — "Regenerating..." first, then `✓ All tests pass` snaps in.
4. **Frame 75-105 (2.5-3.5s):** Large green checkmark scales in from center with a pulse (`0→1.15→1.0`).
5. **Frame 105-150 (3.5-5s):** Hold. Checkmark glows softly. Terminal holds.

### Typography
- Terminal text: JetBrains Mono (or SF Mono fallback), 16px, regular
- Prompt `$`: `#22C55E` (green)
- Commands: `#E2E8F0` (light gray)
- Output: `#94A3B8` (muted gray)
- Success text: `#22C55E`
- Checkmark: JetBrains Mono, 48px, `#22C55E`

### Easing
- Terminal fade-in: `easeOutQuad` over 15 frames
- Character typing: linear, 2 frames per character
- Checkmark scale: `easeOutBack` over 15 frames
- Checkmark glow: `easeInOutSine` on 60-frame cycle

## Narration Sync
> "Code just got that cheap."

Segment: `closing_001` (0.00s - 2.60s) overlapping into `closing_002` (2.94s - 12.28s)

- **0:03** Terminal appears as narration delivers "Code just got that cheap"
- **0:05** `pdd bug` completes — aligns with start of closing_002

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Terminal panel */}
    <Sequence from={0}>
      <FadeIn durationInFrames={15} easing="easeOutQuad">
        <TerminalPanel
          x={360} y={300} width={1200} height={480}
          bg="#111827" border="#1E293B" radius={8}
        >
          <MacOSDots y={315} />

          {/* Line 1: pdd bug */}
          <Sequence from={15}>
            <TypeWriter
              text="$ pdd bug email_validator"
              promptColor="#22C55E" textColor="#E2E8F0"
              font="JetBrains Mono" size={16}
              charsPerFrame={0.5} y={380} x={400}
            />
          </Sequence>

          {/* Line 2: output */}
          <Sequence from={35}>
            <FadeIn durationInFrames={8}>
              <Text text="  Test added: test_rejects_unicode_homoglyphs"
                font="JetBrains Mono" size={16}
                color="#94A3B8" x={400} y={420} />
            </FadeIn>
          </Sequence>

          {/* Line 3: pdd fix */}
          <Sequence from={45}>
            <TypeWriter
              text="$ pdd fix email_validator"
              promptColor="#22C55E" textColor="#E2E8F0"
              font="JetBrains Mono" size={16}
              charsPerFrame={0.5} y={480} x={400}
            />
          </Sequence>

          {/* Line 4: success */}
          <Sequence from={65}>
            <FadeIn durationInFrames={8}>
              <Text text="  Regenerating... ✓ All tests pass"
                font="JetBrains Mono" size={16}
                color="#22C55E" x={400} y={520} />
            </FadeIn>
          </Sequence>
        </TerminalPanel>
      </FadeIn>
    </Sequence>

    {/* Large checkmark */}
    <Sequence from={75}>
      <ScaleSpring from={0} to={1.0} overshoot={1.15}
        durationInFrames={15} easing="easeOutBack">
        <Text text="✓" font="JetBrains Mono" size={48}
          color="#22C55E" x={960} y={640} align="center" />
      </ScaleSpring>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "terminal_animation",
  "commands": [
    { "cmd": "pdd bug email_validator", "output": "Test added: test_rejects_unicode_homoglyphs" },
    { "cmd": "pdd fix email_validator", "output": "Regenerating... ✓ All tests pass" }
  ],
  "terminalBg": "#111827",
  "backgroundColor": "#0A0F1A",
  "successColor": "#22C55E",
  "durationSeconds": 5,
  "narrationSegments": ["closing_001", "closing_002"]
}
```
