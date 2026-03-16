[split:]

# Section 4.4: Prompt Comparison — Dense vs Minimal Split

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:42 – 0:58

## Visual Description
A split-screen comparison showing two ways to achieve the same result. The left panel shows `parser_v1.prompt` — a dense, 50-line prompt specifying everything in exhaustive detail. The right panel shows `parser_v2.prompt` — a minimal 10-line prompt surrounded by dozens of test wall icons. Both panels run `pdd generate parser` and both produce correct output. The visual punchline: the right side achieves the same result with 80% less specification because tests carry the precision burden. This is the practical proof of the tradeoff curve.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Vertical divider: 2px, `rgba(255,255,255,0.12)`, centered at x=960

### Chart/Visual Elements
- **Left Panel — Dense Prompt (x: 0–958)**
  - Header: "Without Tests" — `#EF4444`, 18px, centered at (480, 50)
  - File tab: `parser_v1.prompt` — JetBrains Mono, 13px, `#94A3B8`, with file icon, at (480, 90)
  - Prompt document: 340×380px code block at (480, 310), dark bg `#1A2332`, border `#EF4444` at 0.2 opacity
    - 50 lines of faint text (representing dense spec), `#FFFFFF` at 0.15 opacity
    - Key visible lines (full opacity): "Handle null inputs", "Return sorted", "Validate JSON", "Edge: empty list", "Error: timeout after 100ms"
    - Line count badge: "50 lines" — bottom-right of doc, `#EF4444`, 12px bold
  - Terminal block: 340×80px at (480, 560), dark bg `#0D1117`
    - `$ pdd generate parser` types on → `parser.py generated (247 lines) ✓`
    - Checkmark: `#5AAA6E`
  - Result label: "Works. But 50 lines of spec." — `#94A3B8`, 14px, at (480, 680)

- **Right Panel — Minimal Prompt + Tests (x: 962–1920)**
  - Header: "With Tests" — `#5AAA6E`, 18px, centered at (1440, 50)
  - File tab: `parser_v2.prompt` — JetBrains Mono, 13px, `#94A3B8`, with file icon, at (1440, 90)
  - Prompt document: 200×160px code block at (1440, 280), dark bg `#1A2332`, border `#5AAA6E` at 0.2 opacity
    - 10 lines of text, `#FFFFFF` at 0.3 opacity
    - Key visible lines: "Parse input to AST", "Support JSON + YAML"
    - Line count badge: "10 lines" — bottom-right, `#5AAA6E`, 12px bold
  - Test wall icons: 12 small rounded rectangles (36×18px each) surrounding the prompt document
    - Color: `#D9944A` at 0.4 opacity, border `#D9944A` at 0.6 opacity
    - Arranged: 4 above, 4 below, 2 left, 2 right — forming a visual "wall" around the prompt
    - Counter: "47 tests" — `#D9944A`, 14px bold, positioned below walls
  - Terminal block: 340×100px at (1440, 540), dark bg `#0D1117`
    - Line 1: `$ pdd test parser` → `47 passed ✓` (green)
    - Line 2: `$ pdd generate parser` → `parser.py generated (251 lines) ✓`
  - Result label: "Works. 10 lines of spec. Tests do the rest." — `#94A3B8`, 14px, at (1440, 680)

### Animation Sequence
1. **Frame 0–20 (0–0.67s):** Divider draws top-to-bottom. Headers "Without Tests" and "With Tests" fade in simultaneously.
2. **Frame 20–60 (0.67–2.0s):** File tabs appear. Left: Dense prompt document fades in — dense, imposing, wall of text. Right: Small prompt document fades in — visibly shorter, lighter.
3. **Frame 60–120 (2.0–4.0s):** Left: Key spec lines highlight sequentially (opacity 0.15→1.0) — showing the exhaustive detail required. Line count badge "50 lines" pulses in red. Right: Test wall icons materialize around the prompt, 4-frame stagger, each with a tiny spring-in. Counter "47 tests" fades in.
4. **Frame 120–210 (4.0–7.0s):** Left: Terminal types `$ pdd generate parser` → result appears. Right: Terminal types `$ pdd test parser` → `47 passed ✓` appears in green, then types `$ pdd generate parser` → result appears.
5. **Frame 210–300 (7.0–10.0s):** Both terminals show green checkmarks simultaneously. A brief flash: both sides produced ~250 lines of code. The equivalence is the point.
6. **Frame 300–390 (10.0–13.0s):** Result labels type on below each panel. Left: "Works. But 50 lines of spec." Right: "Works. 10 lines of spec. Tests do the rest."
7. **Frame 390–420 (13.0–14.0s):** An equivalence indicator appears between the panels — a large `=` sign at (960, 400), `#FFFFFF` at 0.5 opacity, 48px, pulsing once.
8. **Frame 420–480 (14.0–16.0s):** Hold. Both panels visible. The visual weight difference is the argument: dense left vs. light-surrounded-by-walls right.

### Typography
- Panel headers: Inter SemiBold, 18px, respective colors
- File tabs: JetBrains Mono, 13px, `#94A3B8`
- Prompt text (visible): JetBrains Mono, 11px, `#FFFFFF` at varying opacity
- Line count badges: Inter Bold, 12px, respective colors
- Terminal text: JetBrains Mono, 12px, `#C9D1D9`
- Terminal commands: JetBrains Mono, 12px, `#79C0FF` (blue for commands)
- Result labels: Inter Regular, 14px, `#94A3B8`
- Test counter: Inter Bold, 14px, `#D9944A`
- Equivalence sign: Inter Bold, 48px, `#FFFFFF` at 0.5 opacity

### Easing
- Divider draw: `easeOutCubic`
- Document fade: `easeOutQuad`
- Line highlight: `easeOutQuad`
- Wall icon spring: `spring({ damping: 18, stiffness: 160 })`
- Terminal type-on: linear (typewriter cadence, 40ms/char)
- Result label type-on: linear
- Equivalence pulse: `easeInOutSine`

## Narration Sync
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Divider */}
    <Sequence from={0} durationInFrames={20}>
      <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
    </Sequence>

    {/* Left Panel — Dense Prompt */}
    <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="Without Tests" color="#EF4444" x={480} />
      </Sequence>
      <Sequence from={20} durationInFrames={40}>
        <FileTab name="parser_v1.prompt" x={480} />
        <PromptDocument lines={50} width={340} height={380} x={480} y={310}
          borderColor="#EF4444" highlightLines={highlightLinesLeft} />
      </Sequence>
      <Sequence from={60} durationInFrames={60}>
        <LineHighlighter lines={highlightLinesLeft} />
        <Badge text="50 lines" color="#EF4444" />
      </Sequence>
      <Sequence from={120} durationInFrames={90}>
        <TerminalBlock commands={leftCommands} x={480} y={560} />
      </Sequence>
      <Sequence from={300} durationInFrames={90}>
        <TypeOnText text="Works. But 50 lines of spec." x={480} y={680} />
      </Sequence>
    </AbsoluteFill>

    {/* Right Panel — Minimal Prompt + Tests */}
    <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="With Tests" color="#5AAA6E" x={1440} />
      </Sequence>
      <Sequence from={20} durationInFrames={40}>
        <FileTab name="parser_v2.prompt" x={1440} />
        <PromptDocument lines={10} width={200} height={160} x={1440} y={280}
          borderColor="#5AAA6E" />
      </Sequence>
      <Sequence from={60} durationInFrames={60}>
        <TestWallIcons count={12} layout="surround" stagger={4}
          target={{ x: 1440, y: 280 }} color="#D9944A" />
        <Badge text="47 tests" color="#D9944A" />
      </Sequence>
      <Sequence from={120} durationInFrames={90}>
        <TerminalBlock commands={rightCommands} x={1440} y={540} />
      </Sequence>
      <Sequence from={300} durationInFrames={90}>
        <TypeOnText text="Works. 10 lines of spec. Tests do the rest." x={1440} y={680} />
      </Sequence>
    </AbsoluteFill>

    {/* Equivalence indicator */}
    <Sequence from={390} durationInFrames={30}>
      <PulsingEquals x={960} y={400} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "leftPanel": {
    "title": "Without Tests",
    "color": "#EF4444",
    "file": "parser_v1.prompt",
    "lineCount": 50,
    "highlightLines": [
      "Handle null inputs",
      "Return sorted",
      "Validate JSON",
      "Edge: empty list",
      "Error: timeout after 100ms"
    ],
    "terminal": [
      { "command": "pdd generate parser", "output": "parser.py generated (247 lines) ✓" }
    ],
    "resultLabel": "Works. But 50 lines of spec."
  },
  "rightPanel": {
    "title": "With Tests",
    "color": "#5AAA6E",
    "file": "parser_v2.prompt",
    "lineCount": 10,
    "visibleLines": ["Parse input to AST", "Support JSON + YAML"],
    "testCount": 47,
    "wallIconCount": 12,
    "terminal": [
      { "command": "pdd test parser", "output": "47 passed ✓" },
      { "command": "pdd generate parser", "output": "parser.py generated (251 lines) ✓" }
    ],
    "resultLabel": "Works. 10 lines of spec. Tests do the rest."
  }
}
```

---
