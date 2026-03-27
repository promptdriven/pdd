[Remotion]

# Section 1.11: Patching vs. Regeneration — Context Window Comparison

**Tool:** Remotion
**Duration:** ~27s (810 frames @ 30fps)
**Timestamp:** 5:57 - 6:24

## Visual Description

A side-by-side comparison showing why regeneration fundamentally solves the context window problem. Two panels, each showing a stylized context window:

**LEFT: "Agentic Patching"**
A context window filled with ~15,000 tokens of raw code. Most blocks are highlighted red (irrelevant code the retrieval system grabbed). A tiny green section shows the actually relevant code. The window is cramped, noisy, wasteful. Label: "15,000 tokens — mostly wrong."

**RIGHT: "PDD Regeneration"**
A context window with a 300-token prompt block (blue), a 2,000-token test block (amber), and a small grounding example (green). The rest of the window is empty — breathing room. Clean, focused, intentional. Label: "2,300 tokens — all curated."

The contrast is stark: one side is cluttered guesswork, the other is surgical precision.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Layout
- Two panels side by side, each 860×600px
- Left panel origin: (60, 200)
- Right panel origin: (1000, 200)
- Panel headers above each

#### Left Panel — Agentic Patching
- Context window outline: `#64748B`, 2px, dashed border
- Fill blocks (code tokens): 15 rows of token blocks
  - Red blocks (irrelevant): `#EF4444` at 0.25, ~80% of blocks
  - Green blocks (relevant): `#5AAA6E` at 0.3, ~5% of blocks
  - Gray blocks (neutral): `#334155` at 0.15, ~15%
- Label: "15,000 tokens — mostly wrong" — Inter 14px, `#EF4444`
- Header: "Agentic Patching" — Inter 20px, bold (700), `#94A3B8`

#### Right Panel — PDD Regeneration
- Context window outline: `#4A90D9`, 2px, solid border
- Prompt block: `#4A90D9` at 0.2, ~60px tall, labeled "Prompt (300 tokens)"
- Test block: `#D9944A` at 0.2, ~100px tall, labeled "Tests (2,000 tokens)"
- Grounding block: `#5AAA6E` at 0.2, ~40px tall, labeled "Grounding example"
- Empty space: `#0F172A` at 0.3, remaining ~400px — labeled "Room to think"
- Label: "2,300 tokens — all curated" — Inter 14px, `#5AAA6E`
- Header: "PDD Regeneration" — Inter 20px, bold (700), `#4A90D9`

### Animation Sequence
1. **Frame 0-60 (0-2s):** Both panel outlines draw. Headers type in.
2. **Frame 60-210 (2-7s):** LEFT panel: token blocks fill in row by row, red blocks appearing — chaotic, overflowing.
3. **Frame 210-360 (7-12s):** RIGHT panel: prompt block slides in (blue), then tests (amber), then grounding (green). Clean, organized. "Room to think" label appears in the empty space.
4. **Frame 360-510 (12-17s):** Both panels fully visible. Labels appear below each.
5. **Frame 510-810 (17-27s):** Hold. The visual comparison speaks for itself.

### Typography
- Panel headers: Inter, 20px, bold (700), respective colors
- Block labels: Inter, 12px, regular (400), respective colors at 0.7
- Comparison labels: Inter, 14px, regular (400), `#EF4444` / `#5AAA6E`
- "Room to think": Inter, 14px, italic, `#64748B` at 0.5

### Easing
- Panel draw: `easeOut(quad)` over 30 frames
- Left blocks fill: `easeOut(quad)`, 3-frame stagger per row
- Right blocks slide-in: `easeOut(cubic)` over 30 frames each
- Labels: `easeOut(quad)` over 20 frames

## Narration Sync
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs."
> "And there's something else. These models are trained on up to 30 times more natural language than code. Natural language is their deepest fluency."

Segments: `part1_economics_023`, `part1_economics_024`

- **356.64s** (seg 023): Panels begin drawing — "Regeneration doesn't have this problem"
- **383.08s** (seg 023 ends): Both panels fully visible
- **383.20s** (seg 024): Hold — "And there's something else"
- **409.62s** (seg 024 ends): Comparison complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={810}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel: Agentic Patching */}
    <Sequence from={0}>
      <ContextWindowPanel
        position={{ x: 60, y: 200 }}
        width={860} height={600}
        header="Agentic Patching"
        headerColor="#94A3B8"
        borderStyle="dashed" borderColor="#64748B"
      >
        <Sequence from={60}>
          <TokenBlockFill
            rows={15}
            distribution={{ red: 0.80, green: 0.05, gray: 0.15 }}
            redColor="#EF4444" greenColor="#5AAA6E"
            staggerPerRow={3}
          />
        </Sequence>
      </ContextWindowPanel>
    </Sequence>

    {/* Right panel: PDD Regeneration */}
    <Sequence from={0}>
      <ContextWindowPanel
        position={{ x: 1000, y: 200 }}
        width={860} height={600}
        header="PDD Regeneration"
        headerColor="#4A90D9"
        borderStyle="solid" borderColor="#4A90D9"
      >
        <Sequence from={210}>
          <SlideIn direction="left" duration={30}>
            <TokenBlock label="Prompt (300 tokens)"
              color="#4A90D9" height={60} />
          </SlideIn>
        </Sequence>
        <Sequence from={250}>
          <SlideIn direction="left" duration={30}>
            <TokenBlock label="Tests (2,000 tokens)"
              color="#D9944A" height={100} />
          </SlideIn>
        </Sequence>
        <Sequence from={290}>
          <SlideIn direction="left" duration={30}>
            <TokenBlock label="Grounding example"
              color="#5AAA6E" height={40} />
          </SlideIn>
        </Sequence>
        <Sequence from={330}>
          <FadeIn duration={20}>
            <Text text="Room to think" style="italic"
              color="#64748B" opacity={0.5} />
          </FadeIn>
        </Sequence>
      </ContextWindowPanel>
    </Sequence>

    {/* Comparison labels */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="15,000 tokens — mostly wrong"
          color="#EF4444" x={490} y={830} align="center" />
        <Text text="2,300 tokens — all curated"
          color="#5AAA6E" x={1430} y={830} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "side_by_side_comparison",
  "chartId": "patching_vs_regeneration",
  "panels": {
    "left": {
      "header": "Agentic Patching",
      "tokenCount": 15000,
      "distribution": { "irrelevant": 0.80, "relevant": 0.05, "neutral": 0.15 },
      "label": "15,000 tokens — mostly wrong",
      "accentColor": "#EF4444"
    },
    "right": {
      "header": "PDD Regeneration",
      "blocks": [
        { "label": "Prompt", "tokens": 300, "color": "#4A90D9" },
        { "label": "Tests", "tokens": 2000, "color": "#D9944A" },
        { "label": "Grounding", "tokens": 200, "color": "#5AAA6E" }
      ],
      "label": "2,300 tokens — all curated",
      "accentColor": "#5AAA6E"
    }
  },
  "narrationSegments": ["part1_economics_023", "part1_economics_024"]
}
```

---
