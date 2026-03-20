[Remotion]

# Section 0.7: Code Regeneration — Delete and Rebuild

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 0:26 - 0:35

## Visual Description

The patched function from scene 0.6 undergoes a dramatic transformation. First: the entire 18-line function selects (all lines highlight in blue). Then it dissolves — each character breaks apart into tiny particles that drift upward and fade, like ash from burning paper. The screen is momentarily empty: just the dark editor background with line numbers and a blinking cursor. Then, from the cursor position, clean new code streams in line by line — 14 lines, no comments, no patches, no scars. The code is structurally equivalent but crisp. In the bottom-right corner, a subtle terminal overlay fades in showing `pdd generate ✓` with a green checkmark. The regeneration feels effortless, inevitable — like the sock that gets replaced instead of repaired.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme)
- Editor chrome: same as scene 0.6

### Chart/Visual Elements

**Particle Dissolution Effect**
- Each character becomes a particle: 2x2px square, same color as the character
- Particles drift upward with random x-jitter: y velocity -40 to -80 px/s, x velocity -20 to +20 px/s
- Particles fade: opacity 1.0 → 0 over 45 frames (1.5s)
- Stagger: dissolution starts from bottom line, propagates upward at 3 frames/line
- Background glow during dissolution: `#F85149` at 0.03, radial, centered on code block

**Clean Code Appearance**
- 14 lines of clean TypeScript — same function, no comments, no workarounds
- Lines type in from left to right: 60 characters/second
- Syntax highlighting identical to scene 0.6 scheme
- Subtle entrance glow: each new line briefly has `#3FB950` at 0.06 background, fading over 10 frames

**Terminal Overlay**
- Position: bottom-right, x: 1400-1880, y: 980-1060
- Background: `#161B22` at 0.9, 8px border-radius
- Border: `#30363D` at 0.4, 1px
- Text: `$ pdd generate processUserInput` — JetBrains Mono 13px, `#8B949E`
- Checkmark: `✓` — JetBrains Mono 13px, `#3FB950`
- Appears after code is fully written

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Selection highlight appears over all 18 lines: `#388BFD` at 0.15 background. Lines highlight simultaneously.
2. **Frame 20-75 (0.67-2.5s):** Particle dissolution. Characters break apart bottom-to-top with 3-frame stagger per line. Particles drift upward and fade. Patch scar highlights dissolve with their characters. The `#F85149` background glow pulses once.
3. **Frame 75-105 (2.5-3.5s):** Empty editor. Just line numbers, dark background, blinking cursor at line 1. The emptiness is deliberate — a breath.
4. **Frame 105-210 (3.5-7s):** Clean code streams in. 14 lines, typed left-to-right at 60 char/s. Each line gets a brief green entrance glow. No comments. No patches. The code is visibly shorter, cleaner.
5. **Frame 210-240 (7-8s):** Terminal overlay fades in at bottom-right. `$ pdd generate processUserInput` appears typed, then `✓` in green.
6. **Frame 240-270 (8-9s):** Hold on the clean code with terminal overlay. The contrast with scene 0.6 is stark.

### Typography
- Code: JetBrains Mono, 18px, `#C9D1D9` (same as scene 0.6)
- Terminal text: JetBrains Mono, 13px, `#8B949E`
- Terminal checkmark: JetBrains Mono, 13px, `#3FB950`

### Easing
- Selection highlight: `easeOut(quad)` — instant feel
- Particle drift: `easeOut(cubic)` — decelerating scatter
- Particle fade: `linear` — steady disappearance
- Code type-in: `linear` — steady stream (mimics real generation)
- Line entrance glow fade: `easeOut(quad)`
- Terminal fade-in: `easeOut(cubic)`

## Narration Sync
> "So why are we still patching?"

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_008` | "So why are we still patching?" | Frame 105 — lands during the empty editor beat, before regeneration begins. The question hangs in the void. |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <EditorChrome background="#0D1117" gutterWidth={200}>
    {/* Phase 1: Selection highlight */}
    <Sequence from={0} durationInFrames={20}>
      <SelectionHighlight
        lines={[1, 18]}
        color="#388BFD"
        opacity={0.15}
      />
      <SyntaxHighlightedCode code={patchedFunction} />
    </Sequence>

    {/* Phase 2: Particle dissolution */}
    <Sequence from={20} durationInFrames={55}>
      <ParticleDissolution
        code={patchedFunction}
        direction="bottom-to-top"
        staggerFrames={3}
        particleSize={2}
        driftVelocity={{ y: [-80, -40], x: [-20, 20] }}
        fadeDuration={45}
      />
      <RadialGlow color="#F85149" opacity={0.03} pulse={true} />
    </Sequence>

    {/* Phase 3: Empty beat */}
    <Sequence from={75} durationInFrames={30}>
      <BlinkingCursor line={1} column={0} color="#58A6FF" />
    </Sequence>

    {/* Phase 4: Clean code streams in */}
    <Sequence from={105} durationInFrames={105}>
      <TypewriterCode
        code={cleanFunction}
        charsPerSecond={60}
        entranceGlow={{ color: "#3FB950", opacity: 0.06, fadeDuration: 10 }}
      />
    </Sequence>

    {/* Phase 5: Terminal overlay */}
    <Sequence from={210} durationInFrames={60}>
      <FadeIn duration={15}>
        <TerminalOverlay
          x={1400} y={980}
          command="pdd generate processUserInput"
          result="✓"
          resultColor="#3FB950"
        />
      </FadeIn>
    </Sequence>
  </EditorChrome>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_editor_animation",
  "phases": [
    {
      "name": "selection",
      "frames": [0, 20],
      "lineRange": [1, 18],
      "highlightColor": "#388BFD",
      "highlightOpacity": 0.15
    },
    {
      "name": "dissolution",
      "frames": [20, 75],
      "effect": "particle_scatter",
      "direction": "bottom_to_top",
      "staggerFramesPerLine": 3,
      "particleSize": 2
    },
    {
      "name": "empty_beat",
      "frames": [75, 105],
      "description": "Empty editor with blinking cursor"
    },
    {
      "name": "regeneration",
      "frames": [105, 210],
      "effect": "typewriter",
      "charsPerSecond": 60,
      "lineCount": 14
    },
    {
      "name": "terminal_confirm",
      "frames": [210, 270],
      "command": "pdd generate processUserInput",
      "result": "✓"
    }
  ],
  "oldCode": {
    "functionName": "processUserInput",
    "lineCount": 18,
    "patchComments": 4
  },
  "newCode": {
    "functionName": "processUserInput",
    "lineCount": 14,
    "patchComments": 0,
    "code": [
      "function processUserInput(raw: string): ProcessedInput {",
      "  const sanitized = raw.trim().toLowerCase();",
      "",
      "  if (!sanitized) {",
      "    return { valid: false, value: '', error: 'empty input' };",
      "  }",
      "",
      "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');",
      "  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);",
      "",
      "  return {",
      "    valid: true,",
      "    value: truncated,",
      "    ...(cleaned !== sanitized && { warning: 'chars stripped' }),",
      "  };",
      "}"
    ]
  },
  "narrationSegments": ["cold_open_008"]
}
```
