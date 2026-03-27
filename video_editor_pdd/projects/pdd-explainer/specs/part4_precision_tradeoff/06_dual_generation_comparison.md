[Remotion]

# Section 4.6: Dual Generation Comparison — Same Output, Different Paths

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:04 - 1:12

## Visual Description

A side-by-side animation showing both prompt approaches generating code — and both producing the same correct output. This drives home that the result is identical; only the effort differs.

**LEFT SIDE:** The 50-line prompt file (miniaturized, amber border) with an arrow pointing down to a generated code block. The code block glows briefly as it appears — clean, correct output. Label: "50-line prompt → Correct code."

**RIGHT SIDE:** The 10-line prompt file (miniaturized, blue border) with 47 test indicators arranged as a frame around it, and an arrow pointing down to an identical generated code block. The code block glows the same way. Label: "10-line prompt + 47 tests → Same correct code."

**Emphasis:** Both code blocks are visually identical — same structure, same glow. But the left side required 5x more prompt effort. A comparison bar appears at bottom: "Prompt effort: 50 lines vs 10 lines" with a visual ratio indicator.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Layout
- Two columns, each 800px wide, 40px center gap
- Left column origin: (80, 80)
- Right column origin: (1040, 80)

#### Left Column — High Prompt Effort
- Miniaturized prompt file: 320×180px, `#D9944A` border at 0.4, filled with faint text lines
- Badge: "50 lines" — `#D9944A`
- Arrow: Downward, `#64748B` at 0.5, 40px tall, centered below prompt
- Generated code block: 320×260px, `#1E293B` background, `#5AAA6E` glow border on reveal
- Code lines: JetBrains Mono, 11px, `#CBD5E1` at 0.7, 12-15 visible lines
- Label: "50-line prompt → Correct code" — Inter, 13px, `#D9944A` at 0.7

#### Right Column — Low Prompt + Tests
- Miniaturized prompt file: 200×120px, `#4A90D9` border at 0.4, compact
- Badge: "10 lines" — `#4A90D9`
- Test wall indicators: 47 small squares (5×5px, `#4A90D9` at 0.5) arranged in rows around the prompt
- Arrow: Downward, `#64748B` at 0.5, 40px tall
- Generated code block: 320×260px, `#1E293B` background, `#5AAA6E` glow border (identical to left)
- Code lines: identical visual structure to left
- Label: "10-line prompt + 47 tests → Same correct code" — Inter, 13px, `#4A90D9` at 0.7

#### Comparison Bar (bottom)
- Position: centered, y: 950, 800px wide
- Left segment: `#D9944A` at 0.3, width proportional to 50 (500px)
- Right segment: `#4A90D9` at 0.3, width proportional to 10 (100px)
- Label: "Prompt effort: 50 lines vs 10 lines" — Inter, 14px, `#94A3B8`
- "5× less" callout on right: Inter, 14px, bold, `#4A90D9`

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Both prompt files appear simultaneously — left large/amber, right compact/blue with test indicators.
2. **Frame 45-90 (1.5-3s):** Arrows draw downward from both prompts.
3. **Frame 90-150 (3-5s):** Code blocks generate simultaneously — lines appear row by row. Both blocks glow green on completion.
4. **Frame 150-195 (5-6.5s):** Labels appear below each column. The identical output is visually confirmed.
5. **Frame 195-210 (6.5-7s):** Comparison bar animates in at bottom — the 5:1 ratio is stark.
6. **Frame 210-240 (7-8s):** Hold. Fade out.

### Typography
- Badges: Inter, 11px, semi-bold (600), respective colors
- Code text: JetBrains Mono, 11px, regular (400), `#CBD5E1` at 0.7
- Column labels: Inter, 13px, regular (400), respective colors at 0.7
- Comparison label: Inter, 14px, regular (400), `#94A3B8`
- "5× less": Inter, 14px, bold (700), `#4A90D9`

### Easing
- Prompt appear: `easeOut(quad)` over 30 frames
- Arrow draw: `easeOut(quad)` over 20 frames
- Code generation: `linear`, 1 line per 4 frames
- Green glow: `easeOut(cubic)` over 15 frames
- Comparison bar: `easeOut(cubic)` over 20 frames
- Fade out: `easeIn(quad)` over 30 frames

## Narration Sync
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segment: `part4_precision_tradeoff_003` (end) into gap before seg 004

- **62.00s**: Both prompts visible, code generating
- **64.00s**: Comparison bar appears — "the mold does the precision work"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left column: 50-line prompt */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <MiniPromptFile
          position={{ x: 240, y: 100 }}
          width={320} height={180}
          borderColor="#D9944A"
          badge="50 lines" lineCount={50}
        />
      </FadeIn>
    </Sequence>

    {/* Right column: 10-line prompt + tests */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <MiniPromptFile
          position={{ x: 1360, y: 130 }}
          width={200} height={120}
          borderColor="#4A90D9"
          badge="10 lines" lineCount={10}
        />
        <TestIndicators
          count={47} dotSize={5}
          color="#4A90D9" opacity={0.5}
          surroundTarget={{ x: 1360, y: 130, w: 200, h: 120 }}
        />
      </FadeIn>
    </Sequence>

    {/* Arrows */}
    <Sequence from={45}>
      <DrawArrow from={[400, 300]} to={[400, 360]}
        color="#64748B" opacity={0.5} />
      <DrawArrow from={[1460, 270]} to={[1460, 360]}
        color="#64748B" opacity={0.5} />
    </Sequence>

    {/* Code blocks */}
    <Sequence from={90}>
      <CodeBlock position={{ x: 240, y: 380 }}
        width={320} height={260}
        lines={generatedCodeLines}
        revealRate={4}
        glowColor="#5AAA6E" glowOnComplete />
      <CodeBlock position={{ x: 1300, y: 380 }}
        width={320} height={260}
        lines={generatedCodeLines}
        revealRate={4}
        glowColor="#5AAA6E" glowOnComplete />
    </Sequence>

    {/* Labels */}
    <Sequence from={150}>
      <FadeIn duration={20}>
        <Text text="50-line prompt → Correct code"
          color="#D9944A" opacity={0.7} x={400} y={670} />
        <Text text="10-line prompt + 47 tests → Same correct code"
          color="#4A90D9" opacity={0.7} x={1460} y={670} />
      </FadeIn>
    </Sequence>

    {/* Comparison bar */}
    <Sequence from={195}>
      <ComparisonBar
        leftValue={50} rightValue={10}
        leftColor="#D9944A" rightColor="#4A90D9"
        label="Prompt effort: 50 lines vs 10 lines"
        callout="5× less" calloutColor="#4A90D9"
        y={950} width={800}
      />
    </Sequence>

    <Sequence from={210}>
      <FadeOut duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "side_by_side_comparison",
  "chartId": "dual_generation_comparison",
  "panels": {
    "left": {
      "label": "High Prompt Effort",
      "promptLines": 50,
      "testCount": 0,
      "accentColor": "#D9944A",
      "result": "correct_code"
    },
    "right": {
      "label": "Low Prompt + Tests",
      "promptLines": 10,
      "testCount": 47,
      "accentColor": "#4A90D9",
      "result": "correct_code"
    }
  },
  "comparison": {
    "metric": "prompt_lines",
    "ratio": "5:1",
    "insight": "Same output, 5× less prompt effort"
  },
  "narrationSegments": ["part4_precision_tradeoff_003"]
}
```

---
