[split:]

# Section 4.6: Prompt Comparison — Dense vs Minimal

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 19:18 - 19:34

## Visual Description
A split-screen comparison of two development approaches. The LEFT side shows a dense, 50-line prompt file (`parser_v1.prompt`) — a tall scrolling document filled with detailed specifications, edge cases, and requirements. The RIGHT side shows a minimal, 10-line prompt file (`parser_v2.prompt`) — a short, clean document specifying only intent — but surrounded by a visible cluster of test file indicators. Below each prompt, a terminal window runs code generation. Both produce the same output: a working parser. The punchline: identical results, but one required 5x the prompt effort. A terminal on the right shows `pdd test parser` with 47 tests passing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, Y: 60-1020, `rgba(255,255,255,0.12)`
- **LEFT Panel (X: 40-940) — Dense Prompt**
  - File tab: "parser_v1.prompt" — JetBrains Mono 13px, `#94A3B8`, on dark tab background `#1E293B`, positioned at (60, 60), 200px wide x 32px tall, rounded top corners 4px
  - Document body: 860px wide x 520px tall, positioned at (60, 92), background `#1E293B`, border `rgba(255,255,255,0.06)` 1px, rounded bottom corners 4px
  - Text lines: 50 lines of simulated prompt text, each 10px tall with 4px line spacing
    - Lines 1-5: Section header style, `#4A90D9` at 0.6 opacity (intent)
    - Lines 6-20: Dense requirement text, `#C8CCD4` at 0.5 opacity
    - Lines 21-35: Edge case specifications, `#E85D75` at 0.4 opacity (red-tinted to suggest tedium)
    - Lines 36-50: Error handling rules, `#C8CCD4` at 0.4 opacity
  - Line count indicator: "50 lines" — JetBrains Mono 11px, `#E85D75` at 0.6 opacity, right-aligned at (920, 96)
  - Terminal below document: 860px wide x 160px tall, at (60, 640), dark background `#0C1222`, green output text
    - Line 1: `$ pdd generate parser` — `#5AAA6E` at 0.7 opacity
    - Line 2: `✓ parser.py generated (247 lines)` — `#5AAA6E` at 0.7 opacity
  - Result label: "Works. But 50 lines of spec." — Inter 15px, `#E85D75` at 0.6 opacity, at (60, 840)

- **RIGHT Panel (X: 980-1880) — Minimal Prompt + Tests**
  - File tab: "parser_v2.prompt" — JetBrains Mono 13px, `#94A3B8`, on dark tab background `#1E293B`, positioned at (1000, 60), 200px wide x 32px tall
  - Document body: 860px wide x 160px tall (much shorter), positioned at (1000, 92), background `#1E293B`, border `rgba(255,255,255,0.06)` 1px
  - Text lines: 10 lines of minimal prompt text
    - Lines 1-3: Intent statement, `#4A90D9` at 0.6 opacity
    - Lines 4-7: Core requirements only, `#C8CCD4` at 0.5 opacity
    - Lines 8-10: Output format, `#C8CCD4` at 0.5 opacity
  - Line count indicator: "10 lines" — JetBrains Mono 11px, `#5AAA6E` at 0.6 opacity
  - Test wall cluster: 12 small file icons (20px x 26px each) arranged in a 4x3 grid below the prompt at Y=280, each labeled with tiny test names ("test_null.py", "test_unicode.py", etc.), `#D9944A` at 0.35 opacity, with wall-like amber border 1px `#D9944A` at 0.5
  - Test count badge: "47 tests" — JetBrains Mono 12px bold, `#D9944A`, centered below the icon grid
  - Terminal below tests: 860px wide x 160px tall, at (1000, 640), dark background `#0C1222`
    - Line 1: `$ pdd test parser` — `#5AAA6E` at 0.7 opacity
    - Line 2: `47 passed ✓` — `#5AAA6E` at 0.8 opacity, bold
    - Line 3: `$ pdd generate parser` — `#5AAA6E` at 0.7 opacity
    - Line 4: `✓ parser.py generated (251 lines)` — `#5AAA6E` at 0.7 opacity
  - Result label: "Works. 10 lines of spec. Tests do the rest." — Inter 15px, `#5AAA6E` at 0.6 opacity, at (1000, 840)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider fades in. Both file tabs appear simultaneously
2. **Frame 20-80 (0.67-2.67s):** LEFT: Dense prompt document body fades in. Lines populate top-to-bottom with a rapid scroll-like reveal (2 lines per frame). Line count "50 lines" fades in. The sheer density is visually apparent
3. **Frame 60-100 (2.0-3.33s):** RIGHT: Minimal prompt document body fades in. 10 lines populate quickly. Line count "10 lines" fades in. The brevity contrasts sharply
4. **Frame 100-160 (3.33-5.33s):** RIGHT: Test wall cluster fades in — icons appear one-by-one with 4-frame stagger (12 icons x 4 frames = 48 frames). Each icon gets a subtle amber border glow on appear. "47 tests" badge pulses in after icons complete
5. **Frame 160-240 (5.33-8.0s):** LEFT terminal types out command and result. RIGHT terminal types out test run (47 passed), then generate command and result. Terminal text appears character-by-character at ~4 chars/frame
6. **Frame 240-340 (8.0-11.33s):** Both terminals complete. A brief animated comparison arrow or "=" sign appears between the two output lines, `#FFFFFF` at 0.4 opacity, indicating equivalent results
7. **Frame 340-420 (11.33-14.0s):** Result labels fade in below each panel. Left: red-tinted "Works. But 50 lines of spec." Right: green-tinted "Works. 10 lines of spec. Tests do the rest."
8. **Frame 420-480 (14.0-16.0s):** Hold. Full comparison visible. The right panel subtly glows with a `rgba(90,170,110,0.03)` vignette suggesting it's the preferred approach

### Typography
- File Tab: JetBrains Mono, 13px, medium (500), `#94A3B8`
- Prompt Text Lines: JetBrains Mono, 10px, regular (400), various colors as specified
- Line Count: JetBrains Mono, 11px, medium (500), respective color
- Terminal Text: JetBrains Mono, 12px, regular (400), `#5AAA6E`
- Test File Labels: JetBrains Mono, 7px, regular (400), `#D9944A` at 0.5 opacity
- Test Count Badge: JetBrains Mono, 12px, bold (700), `#D9944A`
- Result Labels: Inter, 15px, medium (500), respective color at 0.6 opacity

### Easing
- Document body fade: `easeOut(quad)`
- Line population scroll: `linear` (typewriter feel)
- Test icon stagger: `easeOut(quad)` per icon
- Terminal typing: `steps(1)` per character
- Result label fade: `easeOut(quad)`
- Right panel vignette: `easeIn(quad)`

## Narration Sync
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  {/* Divider */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
  </Sequence>

  {/* LEFT: Dense Prompt */}
  <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
    <FileTab name="parser_v1.prompt" x={60} y={60} />
    <Sequence from={20} durationInFrames={60}>
      <PromptDocument
        x={60} y={92} width={860} height={520}
        lineCount={50}
        lineColors={densePromptColors}
        scrollReveal={true}
      />
      <LineCount count={50} color="#E85D75" />
    </Sequence>
    <Sequence from={160} durationInFrames={80}>
      <TerminalWindow x={60} y={640} width={860} height={160}>
        <TypedLine text="$ pdd generate parser" delay={0} />
        <TypedLine text="✓ parser.py generated (247 lines)" delay={30} />
      </TerminalWindow>
    </Sequence>
    <Sequence from={340} durationInFrames={80}>
      <FadeIn>
        <ResultLabel text="Works. But 50 lines of spec." color="#E85D75" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>

  {/* RIGHT: Minimal Prompt + Tests */}
  <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
    <FileTab name="parser_v2.prompt" x={1000} y={60} />
    <Sequence from={60} durationInFrames={40}>
      <PromptDocument
        x={1000} y={92} width={860} height={160}
        lineCount={10}
        lineColors={minimalPromptColors}
      />
      <LineCount count={10} color="#5AAA6E" />
    </Sequence>
    <Sequence from={100} durationInFrames={60}>
      <TestWallCluster
        icons={testFileIcons}
        cols={4} rows={3}
        iconSize={{ w: 20, h: 26 }}
        color="#D9944A"
        staggerFrames={4}
      />
      <TestCountBadge count={47} color="#D9944A" />
    </Sequence>
    <Sequence from={160} durationInFrames={80}>
      <TerminalWindow x={1000} y={640} width={860} height={160}>
        <TypedLine text="$ pdd test parser" delay={0} />
        <TypedLine text="47 passed ✓" delay={20} bold />
        <TypedLine text="$ pdd generate parser" delay={40} />
        <TypedLine text="✓ parser.py generated (251 lines)" delay={60} />
      </TerminalWindow>
    </Sequence>
    <Sequence from={340} durationInFrames={80}>
      <FadeIn>
        <ResultLabel
          text="Works. 10 lines of spec. Tests do the rest."
          color="#5AAA6E"
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>

  {/* Equivalence Indicator */}
  <Sequence from={240} durationInFrames={100}>
    <EqualsIndicator x={960} y={720} color="rgba(255,255,255,0.4)" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "leftPanel": {
    "fileName": "parser_v1.prompt",
    "lineCount": 50,
    "sections": [
      { "lines": [1, 5], "type": "intent", "color": "#4A90D9" },
      { "lines": [6, 20], "type": "requirements", "color": "#C8CCD4" },
      { "lines": [21, 35], "type": "edgeCases", "color": "#E85D75" },
      { "lines": [36, 50], "type": "errorHandling", "color": "#C8CCD4" }
    ],
    "terminal": {
      "commands": ["pdd generate parser"],
      "output": "parser.py generated (247 lines)"
    },
    "resultLabel": "Works. But 50 lines of spec."
  },
  "rightPanel": {
    "fileName": "parser_v2.prompt",
    "lineCount": 10,
    "sections": [
      { "lines": [1, 3], "type": "intent", "color": "#4A90D9" },
      { "lines": [4, 7], "type": "coreRequirements", "color": "#C8CCD4" },
      { "lines": [8, 10], "type": "outputFormat", "color": "#C8CCD4" }
    ],
    "testFiles": [
      "test_null.py", "test_unicode.py", "test_empty.py",
      "test_nested.py", "test_large.py", "test_malformed.py",
      "test_encoding.py", "test_whitespace.py", "test_edge.py",
      "test_perf.py", "test_types.py", "test_format.py"
    ],
    "testCount": 47,
    "terminal": {
      "commands": ["pdd test parser", "pdd generate parser"],
      "output": ["47 passed ✓", "parser.py generated (251 lines)"]
    },
    "resultLabel": "Works. 10 lines of spec. Tests do the rest."
  }
}
```

---
