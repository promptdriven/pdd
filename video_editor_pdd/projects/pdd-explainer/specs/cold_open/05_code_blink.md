[Remotion]

# Section 0.5: Code Blink — Delete and Regenerate

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:20 - 0:28

## Visual Description

Return to the code side. A complex, heavily-patched function fills the screen in a dark IDE-style editor. The function is a mess — inline comments reveal layers of accumulated maintenance: `// fixed null case`, `// workaround for #412`, `// TODO: refactor this`, `// temporary fix (2019)`, `// don't remove — breaks prod`. The code is 18 lines of scar tissue.

The cursor blinks on line 1. A beat of silence. Then: the entire function selects with a blue highlight. Another beat. The selected code DELETES — not line by line, but all at once, the text dissolving into particles that drift downward like ash. The empty space holds for a fraction of a second.

Then clean code types in rapidly — not character by character, but in fast block reveals, line by line. 14 lines. Cleaner. No comments. No workarounds. Just the logic. In the bottom-right corner, a subtle terminal shows `pdd generate ✓` fading in.

The emotional beat: that code was precious because it was expensive. Now it's disposable because generation is cheap.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (GitHub dark theme background)
- Grid lines: N/A (IDE mock-up)

### Chart/Visual Elements

#### IDE Frame
- Editor area: 200px left margin (line numbers), 100px right margin, 80px top (tab bar), 60px bottom (status bar)
- Line numbers: JetBrains Mono, 12px, `#484F58` at 0.4, right-aligned at x: 180
- Tab bar: single tab "user_parser.py" — Inter, 12px, `#C9D1D9` at 0.7, with file icon
- Status bar: `Ln 1, Col 1` — Inter, 10px, `#484F58` at 0.3

#### Old Code (18 lines)
- Font: JetBrains Mono, 14px, line-height 22px
- Syntax colors: keywords `#FF7B72`, strings `#A5D6FF`, functions `#D2A8FF`, comments `#8B949E`, variables `#FFA657`
- Comment annotations (the maintenance scars):
  - Line 3: `# fixed null case` — `#8B949E` at 0.5
  - Line 7: `# workaround for #412` — `#8B949E` at 0.5
  - Line 10: `# TODO: refactor this` — `#EF4444` at 0.5
  - Line 13: `# temporary fix (2019)` — `#8B949E` at 0.5
  - Line 16: `# don't remove — breaks prod` — `#EF4444` at 0.5

#### Selection Highlight
- Full function select: `#1F6FEB` at 0.2, covering all 18 lines

#### Particle Dissolution
- ~200 text particles, each 2-4px, inheriting syntax colors
- Drift direction: downward with slight random horizontal wobble
- Gravity: 0.3px/frame acceleration
- Fade: each particle fades from full opacity to 0 over 45 frames

#### New Code (14 lines)
- Same font and syntax colors as old code
- No comment annotations — clean, focused logic
- Appears in 3 block reveals: lines 1-5, lines 6-10, lines 11-14

#### Terminal Snippet
- Position: bottom-right corner (1750, 1010)
- Text: `pdd generate ✓` — JetBrains Mono, 11px, `#5AAA6E` at 0.4
- Green checkmark: `#5AAA6E`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Old code is fully visible. Cursor blinks at line 1. The maintenance scars are readable. Hold — let the viewer absorb the mess.
2. **Frame 30-45 (1-1.5s):** Cursor blink. Selection highlight washes over all 18 lines — a blue tint sweeps top to bottom.
3. **Frame 45-60 (1.5-2s):** Beat. Selected code holds. Tension.
4. **Frame 60-90 (2-3s):** DELETE. All text dissolves into particles simultaneously. Particles drift downward with slight wobble. Colors scatter. The editor is empty.
5. **Frame 90-105 (3-3.5s):** Empty editor holds. Just line numbers and the blinking cursor. The void.
6. **Frame 105-120 (3.5-4s):** New code block 1 (lines 1-5) appears — fast fade-in, 0.15s per block.
7. **Frame 120-135 (4-4.5s):** New code block 2 (lines 6-10) appears.
8. **Frame 135-150 (4.5-5s):** New code block 3 (lines 11-14) appears. Clean. No comments. Focused.
9. **Frame 150-180 (5-6s):** Terminal snippet `pdd generate ✓` fades in at bottom-right.
10. **Frame 180-240 (6-8s):** Hold on clean code. The difference is visceral — 14 lines vs 18, zero maintenance comments.

### Typography
- Code: JetBrains Mono, 14px, syntax-highlighted
- Line numbers: JetBrains Mono, 12px, `#484F58` at 0.4
- Tab label: Inter, 12px, `#C9D1D9` at 0.7
- Terminal snippet: JetBrains Mono, 11px, `#5AAA6E` at 0.4

### Easing
- Selection sweep: `easeOut(quad)` over 15 frames
- Particle dissolution: each particle uses `easeIn(quad)` for gravity, `linear` for horizontal drift
- Particle fade: `easeIn(cubic)` over 45 frames
- New code block reveal: `easeOut(cubic)` opacity 0→1 over 12 frames per block
- Terminal fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "Code just got that cheap."

Segment: `cold_open_004`

- **0:20** ("Code"): Cursor blinks on the patched function. The mess is visible.
- **0:21** ("just got"): Selection highlight sweeps over code. The delete is coming.
- **0:22** ("that cheap"): Code dissolves into particles. Empty editor.
- **0:24** (silence): New code types in rapidly. Clean, focused.
- **0:26** (silence): Terminal shows `pdd generate ✓`. Hold on the transformation.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    <IDEChrome tab="user_parser.py" statusLine="Ln 1, Col 1">
      {/* Old code — visible initially, dissolves */}
      <Sequence from={0} durationInFrames={90}>
        <CodeBlock
          code={oldCodeLines}
          font="JetBrains Mono" size={14}
          syntaxTheme="github-dark"
          lineNumberColor="#484F58"
        />
        {/* Selection highlight */}
        <Sequence from={30}>
          <SelectionHighlight
            lines={[1, 18]} color="#1F6FEB" opacity={0.2}
            sweepDuration={15}
          />
        </Sequence>
      </Sequence>

      {/* Particle dissolution */}
      <Sequence from={60} durationInFrames={45}>
        <ParticleDissolve
          sourceText={oldCodeLines}
          particleCount={200}
          particleSize={[2, 4]}
          gravity={0.3}
          drift={{ x: [-1, 1], y: [0, 0] }}
          fadeDuration={45}
        />
      </Sequence>

      {/* New code — block reveals */}
      <Sequence from={105}>
        <BlockReveal lines={[1, 5]} delay={0} duration={12}>
          <CodeBlock code={newCodeBlock1}
            font="JetBrains Mono" size={14}
            syntaxTheme="github-dark" />
        </BlockReveal>
        <BlockReveal lines={[6, 10]} delay={15} duration={12}>
          <CodeBlock code={newCodeBlock2}
            font="JetBrains Mono" size={14}
            syntaxTheme="github-dark" />
        </BlockReveal>
        <BlockReveal lines={[11, 14]} delay={30} duration={12}>
          <CodeBlock code={newCodeBlock3}
            font="JetBrains Mono" size={14}
            syntaxTheme="github-dark" />
        </BlockReveal>
      </Sequence>

      {/* Terminal snippet */}
      <Sequence from={150}>
        <FadeIn duration={20}>
          <TerminalSnippet
            text="pdd generate ✓" font="JetBrains Mono"
            size={11} color="#5AAA6E" opacity={0.4}
            x={1750} y={1010}
          />
        </FadeIn>
      </Sequence>
    </IDEChrome>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "code_animation",
  "chartId": "code_blink_regenerate",
  "ide": {
    "theme": "github-dark",
    "background": "#0D1117",
    "font": "JetBrains Mono",
    "fontSize": 14
  },
  "oldCode": {
    "lineCount": 18,
    "filename": "user_parser.py",
    "maintenanceComments": [
      { "line": 3, "text": "# fixed null case" },
      { "line": 7, "text": "# workaround for #412" },
      { "line": 10, "text": "# TODO: refactor this" },
      { "line": 13, "text": "# temporary fix (2019)" },
      { "line": 16, "text": "# don't remove — breaks prod" }
    ]
  },
  "newCode": {
    "lineCount": 14,
    "commentCount": 0,
    "revealBlocks": [[1, 5], [6, 10], [11, 14]]
  },
  "dissolution": {
    "particleCount": 200,
    "gravity": 0.3,
    "fadeDuration": 45
  },
  "terminalCommand": "pdd generate ✓",
  "narrationSegments": ["cold_open_004"]
}
```

---
