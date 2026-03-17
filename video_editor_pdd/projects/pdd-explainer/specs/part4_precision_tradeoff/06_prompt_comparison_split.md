[split:]

# Section 4.6: Prompt Comparison Split — Dense vs Minimal

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 19:24 - 19:38

## Visual Description

A vertical split screen shows the same module specified two different ways. LEFT panel shows `parser_v1.prompt` — a long, dense prompt file with 50 lines of tightly packed requirements. The text is small and overwhelming. It specifies edge cases, error formats, null handling, unicode behavior, whitespace rules — everything a developer would normally put in tests. A red-amber stress indicator glows at the edges.

RIGHT panel shows `parser_v2.prompt` — a minimal, 10-line prompt with generous whitespace. Just a few clean requirements: "Parse JSON input per RFC 7159", "Return structured AST", "Handle errors gracefully." Below this prompt, a terminal window shows `$ pdd test parser` running with 47 green checkmarks scrolling past. The tests are doing the constraint work.

The pivotal moment: both panels generate code simultaneously (a brief code-generation animation), and both produce the same correct output. The dense prompt and minimal-plus-tests approaches achieve identical results — but one is 5x shorter.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "FEW TESTS" — Inter, 14px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, centered at y: 35
- RIGHT: "MANY TESTS" — Inter, 14px, semi-bold (600), `#22C55E` at 0.5, letter-spacing 2px, centered at y: 35

#### Left Panel — Dense Prompt (x: 0 to x: 958)
- Background: `#0F172A`
- **File tab:** `parser_v1.prompt` — JetBrains Mono, 11px, `#D9944A` at 0.5, at y: 70
  - Tab underline: 2px, `#D9944A` at 0.3
- **Prompt content:** 50 lines of dense requirement text
  - Font: JetBrains Mono, 9px, `#94A3B8` at 0.5
  - Line height: 14px (cramped)
  - Visible lines ~30 at a time, scrolling slowly
  - Sample lines:
    - `"Parse JSON input. Must handle:`
    - `"- null values → return NullNode"`
    - `"- empty strings → raise EmptyInputError"`
    - `"- unicode escapes → decode to UTF-8"`
    - `"- nested depth > 100 → raise DepthError"`
    - `"- trailing commas → reject with position"`
    - `"- duplicate keys → keep last occurrence"`
    - ...continues for 50 lines
  - Line numbers: `#475569` at 0.3, right-aligned at x: 50
- **Line count:** "50 lines" — Inter, 11px, `#EF4444` at 0.5, bottom-left at (60, 900)
- **Stress indicator:** Subtle red glow along left and right edges of panel
  - `#EF4444` at 0.04, 40px wide gradient from edges

#### Right Panel — Minimal Prompt + Tests (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **File tab:** `parser_v2.prompt` — JetBrains Mono, 11px, `#22C55E` at 0.5, at y: 70
  - Tab underline: 2px, `#22C55E` at 0.3
- **Prompt content:** 10 lines with generous whitespace
  - Font: JetBrains Mono, 9px, `#94A3B8` at 0.5
  - Line height: 20px (spacious)
  - Sample lines:
    - `"Parse JSON input according to RFC 7159."`
    - `""`
    - `"Return a structured AST with typed nodes."`
    - `""`
    - `"Handle malformed input with clear error"`
    - `"messages including line and column position."`
    - `""`
    - `"Optimize for readability over performance."`
  - Line numbers: `#475569` at 0.3
- **Line count:** "10 lines" — Inter, 11px, `#22C55E` at 0.5, bottom-left at (60, 500)
- **Terminal window:** Positioned at y: 550-900
  - Background: `#0A0F1A`, 1px border `#1E293B`
  - Header bar: `#1E293B` at 0.3, with three dots (red/yellow/green)
  - `$ pdd test parser` — JetBrains Mono, 10px, `#94A3B8` at 0.5
  - Test results scrolling:
    - `✓ parses valid JSON` — `#22C55E` at 0.5
    - `✓ handles null values` — `#22C55E` at 0.5
    - `✓ rejects trailing commas` — `#22C55E` at 0.5
    - ...47 lines total
  - Summary: `47/47 passing` — JetBrains Mono, 11px, `#22C55E` at 0.7

#### Code Generation Beat
- Both panels simultaneously show a brief generation flash at Frame 300
- A wave of light sweeps downward through both panels
- Below each prompt, a small code output appears: identical bracket structure
- Both labeled: "Output: identical ✓" — Inter, 10px, `#22C55E` at 0.5

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-60 (0.67-2s):** File tabs appear. LEFT: Dense prompt text begins rendering, line by line, fast. RIGHT: Minimal prompt text renders, spacious.
3. **Frame 60-160 (2-5.33s):** LEFT: Prompt continues scrolling — lines keep coming. The density is overwhelming. Stress glow appears at edges. RIGHT: Prompt is already fully visible. Terminal window appears below.
4. **Frame 160-240 (5.33-8s):** LEFT: Still scrolling. Line count climbs: "38 lines... 45 lines... 50 lines." RIGHT: Test results scroll in terminal — green checkmarks accumulating. "12/47... 28/47... 47/47 passing."
5. **Frame 240-280 (8-9.33s):** Both sides settled. LEFT: "50 lines" badge visible, red stress glow. RIGHT: "10 lines" badge + "47/47 passing" in green.
6. **Frame 280-340 (9.33-11.33s):** Code generation beat — light wave sweeps both panels. Identical code output appears below each.
7. **Frame 340-380 (11.33-12.67s):** "Output: identical ✓" labels appear on both sides.
8. **Frame 380-420 (12.67-14s):** Hold. The visual argument: 50 lines alone = 10 lines + 47 tests. Same result.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- File tabs: JetBrains Mono, 11px, respective colors at 0.5
- Prompt text: JetBrains Mono, 9px, `#94A3B8` at 0.5
- Line numbers: `#475569` at 0.3
- Line count badges: Inter, 11px, respective colors at 0.5
- Terminal text: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Test results: JetBrains Mono, 10px, `#22C55E` at 0.5
- Output labels: Inter, 10px, `#22C55E` at 0.5

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Text rendering: `linear` (typewriter style, 2 lines/second for dense, instant for minimal)
- Stress glow: `easeIn(quad)` fade to 0.04 over 60 frames
- Terminal scroll: `linear` continuous
- Generation flash: `easeOut(expo)` sweep, 15 frames
- Badge/label fade: `easeOut(quad)` over 15 frames

## Narration Sync
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segment: `part4_006`

- **19:24** ("your prompt needs to specify everything"): Dense prompt scrolling, lines accumulating
- **19:28** ("Edge cases. Error handling."): Specific lines highlighted in dense prompt
- **19:32** ("the prompt only needs to specify intent"): Minimal prompt fully visible, terminal active
- **19:36** ("The tests handle the constraints"): Both outputs identical, contrast fully visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Dense prompt */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="FEW TESTS" color="#D9944A"
          opacity={0.5} letterSpacing={2} y={35} />

        <FileTab name="parser_v1.prompt" color="#D9944A"
          opacity={0.5} y={70} underline={true} />

        <Sequence from={20}>
          <ScrollingCode lines={densePromptLines}
            font="JetBrains Mono" size={9}
            color="#94A3B8" lineHeight={14}
            lineNumbers={true} scrollSpeed={1.5}
            visibleLines={30} />
        </Sequence>

        <StressGlow color="#EF4444" opacity={0.04}
          edgeWidth={40} appearAt={100} />

        <Sequence from={240}>
          <Badge text="50 lines" color="#EF4444"
            position={[60, 900]} />
        </Sequence>
      </AbsoluteFill>
    </Panel>

    <SplitLine x={960} color="#334155" opacity={0.25}
      drawDuration={15} />

    {/* Right panel — Minimal prompt + tests */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="MANY TESTS" color="#22C55E"
          opacity={0.5} letterSpacing={2} y={35} />

        <FileTab name="parser_v2.prompt" color="#22C55E"
          opacity={0.5} y={70} underline={true} />

        <Sequence from={20}>
          <StaticCode lines={minimalPromptLines}
            font="JetBrains Mono" size={9}
            color="#94A3B8" lineHeight={20}
            lineNumbers={true} />
        </Sequence>

        <Badge text="10 lines" color="#22C55E"
          position={[60, 500]} appearAt={160} />

        <Sequence from={120}>
          <TerminalWindow y={550} height={350}
            command="pdd test parser"
            results={testResults}
            scrollSpeed={2}
            summaryText="47/47 passing"
            summaryColor="#22C55E" />
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Code generation flash */}
    <Sequence from={280}>
      <GenerationFlash duration={15} color="#E2E8F0" />
      <Sequence from={20}>
        <IdenticalOutputLabel text="Output: identical ✓"
          color="#22C55E" leftX={480} rightX={1440}
          y={950} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "label": "FEW TESTS",
    "fileName": "parser_v1.prompt",
    "lineCount": 50,
    "testCount": 5,
    "concept": "Without tests, the prompt must exhaustively specify every edge case and behavior",
    "stressIndicator": true,
    "color": "#D9944A",
    "background": "#0F172A"
  },
  "rightPanel": {
    "label": "MANY TESTS",
    "fileName": "parser_v2.prompt",
    "lineCount": 10,
    "testCount": 47,
    "concept": "With comprehensive tests, the prompt only needs to state intent — tests handle constraints",
    "terminal": {
      "command": "pdd test parser",
      "result": "47/47 passing"
    },
    "color": "#22C55E",
    "background": "#0A0F1A"
  },
  "codeGenerationBeat": {
    "outputIdentical": true,
    "label": "Output: identical ✓"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part4_006"]
}
```

---
