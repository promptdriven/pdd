[split:]

# Section 4.4: Detailed Prompt vs Minimal Prompt — Side-by-Side Comparison

**Tool:** Split
**Duration:** ~11s (325 frames @ 30fps)
**Timestamp:** 0:47 - 0:58

## Visual Description

A split screen comparing two prompt files side-by-side — one verbose and one minimal — demonstrating the precision tradeoff in practice.

**LEFT — "DETAILED PROMPT (FEW TESTS)":** A code editor showing `parser_v1.prompt` — 50 lines of dense requirements. The file is visually heavy: long paragraphs of natural language, embedded edge-case descriptions, error-handling rules, formatting constraints. A line counter shows "50 lines". Below: a small terminal showing `pdd test parser` with "3 tests passing" in amber. The few tests mean the prompt must carry all the burden.

**RIGHT — "MINIMAL PROMPT (MANY TESTS)":** A code editor showing `parser_v2.prompt` — just 10 lines. Clean, sparse, focused on intent. Below: a terminal showing `pdd test parser` with "47 tests passing" in teal. The many tests are the real spec — the prompt just points the direction. Test names scroll briefly to show coverage breadth.

The split holds as both prompts "generate code" simultaneously — code output streams appear below each editor, and both produce the same ✓ checkmark. The point: both yield correct code, but one required 5× more prompt effort.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Detailed Prompt
- Header: "DETAILED PROMPT" — Inter, 14px, bold, `#F59E0B` at 0.7, y: 40
- Subheader: "(Few Tests)" — Inter, 11px, `#F59E0B` at 0.4, y: 60
- Code editor: 860×480px, bg `#1E1E2E`, rounded 6px, border `#334155` at 0.2
  - Title bar: `parser_v1.prompt` — JetBrains Mono, 11px, `#94A3B8`
  - Content: 50 lines of dense text, JetBrains Mono, 9px, `#D4D4D4` at 0.7
  - Line numbers: `#475569` at 0.3
  - Highlighted sections: requirement blocks in `#F59E0B` at 0.08 bg
- Line counter: "50 lines" — Inter, 12px, bold, `#F59E0B` at 0.6
- Terminal: 860×120px, bg `#0D1117`, rounded 4px, below editor
  - `$ pdd test parser` — JetBrains Mono, 11px, `#94A3B8`
  - `✓ 3 tests passing` — JetBrains Mono, 11px, `#F59E0B`

#### Right Panel — Minimal Prompt
- Header: "MINIMAL PROMPT" — Inter, 14px, bold, `#2DD4BF` at 0.7, y: 40
- Subheader: "(Many Tests)" — Inter, 11px, `#2DD4BF` at 0.4, y: 60
- Code editor: 860×480px, bg `#1E1E2E`, rounded 6px, border `#334155` at 0.2
  - Title bar: `parser_v2.prompt` — JetBrains Mono, 11px, `#94A3B8`
  - Content: 10 lines of clean text, JetBrains Mono, 9px, `#D4D4D4` at 0.7
  - Line numbers: `#475569` at 0.3
  - Large empty space below text — deliberate, showing how little is needed
- Line counter: "10 lines" — Inter, 12px, bold, `#2DD4BF` at 0.6
- Terminal: 860×120px, bg `#0D1117`, rounded 4px, below editor
  - `$ pdd test parser` — JetBrains Mono, 11px, `#94A3B8`
  - `✓ 47 tests passing` — JetBrains Mono, 11px, `#2DD4BF`
  - Test names briefly scroll: `test_parse_basic`, `test_parse_nested`, `test_error_invalid_token`, etc.

#### Code Generation Overlay (Phase 2)
- Both editors get a "Generating..." overlay
- Code streams appear below terminals on both sides
- Both produce `✓ Correct output` — Inter, 14px, bold, `#22C55E`
- Summary: "Same result. 5× less prompt." — Inter, 16px, bold, `#E2E8F0`, centered bottom

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in. Headers appear.
2. **Frame 15-90 (0.5-3s):** Left editor appears. 50 lines of dense prompt scroll into view. Line counter: "50 lines".
3. **Frame 90-150 (3-5s):** Left terminal: `pdd test parser` → "3 tests passing" in amber.
4. **Frame 150-210 (5-7s):** Right editor appears. 10 clean lines. Empty space visible. Line counter: "10 lines".
5. **Frame 210-250 (7-8.3s):** Right terminal: `pdd test parser` → "47 tests passing" in teal. Test names briefly scroll.
6. **Frame 250-290 (8.3-9.7s):** Both sides: "Generating..." overlays. Code streams appear.
7. **Frame 290-325 (9.7-10.8s):** Both produce `✓ Correct output`. Summary label appears.

### Typography
- Headers: Inter, 14px, bold (700), respective colors
- Subheaders: Inter, 11px, respective colors at 0.4
- Code: JetBrains Mono, 9px, `#D4D4D4` at 0.7
- File titles: JetBrains Mono, 11px, `#94A3B8`
- Terminal: JetBrains Mono, 11px, respective colors
- Line counter: Inter, 12px, bold (700), respective colors
- Summary: Inter, 16px, bold (700), `#E2E8F0`

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Editor appear: `easeOut(cubic)` over 20 frames
- Text scroll: linear, 1 line per 1.5 frames
- Terminal output: `easeOut(quad)` over 15 frames
- Test name scroll: linear, 3 frames per name
- Generation overlay: `easeOut(quad)` over 10 frames
- Checkmark: `spring(damping: 12)` over 15 frames
- Summary: `easeOut(quad)` over 20 frames

## Narration Sync
> "This is why test coverage isn't just quality assurance in PDD. It's precision engineering. Each test is a wall."
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segments: `part4_precision_tradeoff_007`, `part4_precision_tradeoff_008`

- **47.42s** (seg 007): Split appears, left editor (detailed prompt) visible
- **52s**: Right editor (minimal prompt) appears, contrast visible
- **55s**: Code generation begins on both sides
- **58.24s** (seg 007 ends / seg 008 starts): Both produce correct output
- **64.46s** (seg 008 ends): Summary label visible, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={325}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — Detailed Prompt */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="DETAILED PROMPT" font="Inter" size={14}
          weight={700} color="#F59E0B" opacity={0.7}
          x={479} y={40} align="center" />
        <Text text="(Few Tests)" font="Inter" size={11}
          color="#F59E0B" opacity={0.4}
          x={479} y={60} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <CodeEditor x={49} y={80} width={860} height={480}
          filename="parser_v1.prompt" lines={50}
          font="JetBrains Mono" fontSize={9}
          bg="#1E1E2E" border="#334155" textColor="#D4D4D4"
          highlightColor="#F59E0B" highlightOpacity={0.08}
          scrollDuration={75} />
        <Text text="50 lines" font="Inter" size={12}
          weight={700} color="#F59E0B" opacity={0.6}
          x={870} y={570} align="right" />
      </Sequence>
      <Sequence from={90}>
        <Terminal x={49} y={580} width={860} height={120}
          commands={[
            { cmd: "pdd test parser", delay: 10 },
            { output: "✓ 3 tests passing", color: "#F59E0B", delay: 20 }
          ]} />
      </Sequence>
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — Minimal Prompt */}
    <Panel x={962} width={958}>
      <FadeIn duration={15}>
        <Text text="MINIMAL PROMPT" font="Inter" size={14}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={479} y={40} align="center" />
        <Text text="(Many Tests)" font="Inter" size={11}
          color="#2DD4BF" opacity={0.4}
          x={479} y={60} align="center" />
      </FadeIn>
      <Sequence from={150}>
        <CodeEditor x={49} y={80} width={860} height={480}
          filename="parser_v2.prompt" lines={10}
          font="JetBrains Mono" fontSize={9}
          bg="#1E1E2E" border="#334155" textColor="#D4D4D4"
          showEmptySpace={true} />
        <Text text="10 lines" font="Inter" size={12}
          weight={700} color="#2DD4BF" opacity={0.6}
          x={870} y={570} align="right" />
      </Sequence>
      <Sequence from={210}>
        <Terminal x={49} y={580} width={860} height={120}
          commands={[
            { cmd: "pdd test parser", delay: 10 },
            { output: "✓ 47 tests passing", color: "#2DD4BF", delay: 15 },
            { scroll: ["test_parse_basic", "test_parse_nested", "test_error_invalid_token", "test_edge_empty_input", "test_unicode_handling"], color: "#2DD4BF", opacity: 0.3, delay: 3 }
          ]} />
      </Sequence>
    </Panel>

    {/* Code generation overlay */}
    <Sequence from={250}>
      <GenerationOverlay
        leftResult="✓ Correct output" rightResult="✓ Correct output"
        resultColor="#22C55E" duration={40} />
    </Sequence>

    {/* Summary */}
    <Sequence from={290}>
      <FadeIn duration={20}>
        <Text text="Same result. 5× less prompt."
          font="Inter" size={16} weight={700} color="#E2E8F0"
          x={960} y={1000} align="center" />
      </FadeIn>
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
    "header": "DETAILED PROMPT",
    "headerColor": "#F59E0B",
    "filename": "parser_v1.prompt",
    "lineCount": 50,
    "testCount": 3,
    "thematicRole": "verbose_specification"
  },
  "rightPanel": {
    "header": "MINIMAL PROMPT",
    "headerColor": "#2DD4BF",
    "filename": "parser_v2.prompt",
    "lineCount": 10,
    "testCount": 47,
    "thematicRole": "test_driven_specification"
  },
  "outcome": {
    "both_correct": true,
    "promptReduction": "5×",
    "summary": "Same result. 5× less prompt."
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_007", "part4_precision_tradeoff_008"]
}
```

---
