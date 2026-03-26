[split:]

# Section 1.9: Patching vs Regeneration — Context Window Comparison

**Tool:** Split
**Duration:** ~26s (780 frames @ 30fps)
**Timestamp:** 6:01 - 6:27

## Visual Description

A vertical split screen showing the fundamental difference in how agentic patching and PDD regeneration use the context window. This is the practical "so what do you do about it?" visual.

**LEFT — "Agentic Patching":** A context window visualization filled with 15,000 tokens of code. Red highlights mark irrelevant sections (~60% of the window). A tiny green section shows the relevant code. The window is cramped, noisy, wasteful. Label: "15,000 tokens consumed. ~40% relevant."

**RIGHT — "PDD Regeneration":** A context window with a 300-token prompt at the top, 2,000 tokens of tests below it, and a small grounding example. The rest is empty — clean white space. The window is spacious, focused, efficient. Label: "2,300 tokens consumed. 100% curated."

The split holds as a compression animation plays: twenty code blocks try to fit into a context window (they overflow), then compress into twenty compact prompt blocks (they all fit with room to spare).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Agentic Patching
- Header: "AGENTIC PATCHING" — Inter, 16px, bold, `#EF4444` at 0.7, y: 50
- Context window: 850×680px, bg `#1E1E2E`, border `#EF4444` at 0.2, rounded 6px
- Content: dense syntax-highlighted code, JetBrains Mono, 8px
  - Red overlay blocks (~60%): `#EF4444` at 0.15 — irrelevant code
  - Green section (~10%): `#22C55E` at 0.15 — relevant code
  - Gray sections (~30%): `#94A3B8` at 0.05 — partially relevant
- Token count: "15,000 tokens consumed" — Inter, 12px, `#EF4444` at 0.6
- Relevance: "~40% relevant" — Inter, 12px, `#EF4444` at 0.5

#### Right Panel — PDD Regeneration
- Header: "PDD REGENERATION" — Inter, 16px, bold, `#2DD4BF` at 0.7, y: 50
- Context window: 850×680px, bg `#0F1E1E`, border `#2DD4BF` at 0.2, rounded 6px
- Content blocks (vertically stacked with generous spacing):
  - Prompt block: 300 tokens, clean text, `#2DD4BF` at 0.5, ~80px tall
  - Test block: 2,000 tokens, structured, `#2DD4BF` at 0.4, ~200px tall
  - Grounding example: small, `#2DD4BF` at 0.3, ~60px tall
  - Remaining space: empty `#0F1E1E` — deliberately empty, labeled "Room to think"
- Token count: "2,300 tokens consumed" — Inter, 12px, `#2DD4BF` at 0.6
- Relevance: "100% curated" — Inter, 12px, `#2DD4BF` at 0.5

#### Compression Animation (Phase 2, overlays on top of split)
- 20 code blocks float from left panel, overflow their window boundary
- Blocks compress into 20 compact prompt blocks
- Prompt blocks float into right panel, all fit with room to spare
- Counter: "Same system. 5-10× more fits." — Inter, 16px, bold, `#E2E8F0`

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in.
2. **Frame 15-180 (0.5-6s):** Left panel fills with dense code. Red/green highlights appear. Header and labels.
3. **Frame 180-360 (6-12s):** Right panel fills with clean prompt/test/grounding blocks. Empty space visible. Header and labels.
4. **Frame 360-480 (12-16s):** Token counts appear on both sides. The 15k vs 2.3k contrast lands.
5. **Frame 480-660 (16-22s):** Compression animation: 20 code blocks → try to fit → overflow → compress → 20 prompt blocks → fit easily.
6. **Frame 660-780 (22-26s):** "Same system. 5-10× more fits." label. Hold.

### Typography
- Headers: Inter, 16px, bold (700), respective colors
- Code: JetBrains Mono, 8px, syntax-highlighted
- Prompt text: Inter, 11px, `#2DD4BF`
- Token counts: Inter, 12px, respective colors
- Compression label: Inter, 16px, bold (700), `#E2E8F0`

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Code fill: linear rapid, 0.3s
- Prompt blocks: `easeOut(quad)` per block, staggered 15 frames
- Red/green highlights: `easeOut(quad)` over 20 frames
- Compression animation: `easeInOut(back)` — blocks shrink with slight overshoot
- Counter: `easeOut(quad)` over 20 frames

## Narration Sync
> "I saw this firsthand. A 3,000-line Python module I maintained for two years? Claude Code rewrote it in three minutes — from a 15-line prompt and a test suite."
> "Research also confirms. Modules around 300 lines can be reliably regenerated from prompts of 15 to 50 lines..."

Segments: `part1_economics_029`, `part1_economics_030`

- **388.10s** ("I saw this firsthand"): Split appears, left panel filling
- **395s** ("Claude Code rewrote it"): Right panel filling, contrast visible
- **413.28s** ("Research also confirms"): Compression animation playing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={780}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — Agentic Patching */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="AGENTIC PATCHING" font="Inter" size={16}
          weight={700} color="#EF4444" opacity={0.7}
          x={479} y={50} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <ContextWindow x={55} y={80} width={850} height={680}
          bg="#1E1E2E" border="#EF4444" borderOpacity={0.2}
          content="dense_code_with_highlights"
          highlights={[
            { type: "irrelevant", color: "#EF4444", opacity: 0.15, percent: 60 },
            { type: "relevant", color: "#22C55E", opacity: 0.15, percent: 10 },
            { type: "partial", color: "#94A3B8", opacity: 0.05, percent: 30 }
          ]} />
      </Sequence>
      <Sequence from={360}>
        <FadeIn duration={15}>
          <Text text="15,000 tokens consumed" font="Inter" size={12}
            color="#EF4444" opacity={0.6} x={479} y={790} align="center" />
          <Text text="~40% relevant" font="Inter" size={12}
            color="#EF4444" opacity={0.5} x={479} y={810} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — PDD Regeneration */}
    <Panel x={962} width={958}>
      <FadeIn duration={15}>
        <Text text="PDD REGENERATION" font="Inter" size={16}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={479} y={50} align="center" />
      </FadeIn>
      <Sequence from={180}>
        <ContextWindow x={55} y={80} width={850} height={680}
          bg="#0F1E1E" border="#2DD4BF" borderOpacity={0.2}
          content="prompt_blocks"
          blocks={[
            { label: "Prompt", tokens: 300, height: 80, color: "#2DD4BF", opacity: 0.5 },
            { label: "Tests", tokens: 2000, height: 200, color: "#2DD4BF", opacity: 0.4 },
            { label: "Grounding example", tokens: 100, height: 60, color: "#2DD4BF", opacity: 0.3 }
          ]}
          emptyLabel="Room to think" />
      </Sequence>
      <Sequence from={360}>
        <FadeIn duration={15}>
          <Text text="2,300 tokens consumed" font="Inter" size={12}
            color="#2DD4BF" opacity={0.6} x={479} y={790} align="center" />
          <Text text="100% curated" font="Inter" size={12}
            color="#2DD4BF" opacity={0.5} x={479} y={810} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>

    {/* Compression animation overlay */}
    <Sequence from={480}>
      <CompressionAnimation
        codeBlocks={20} promptBlocks={20}
        overflowDuration={40} compressDuration={60} fitDuration={40}
        codeColor="#EF4444" promptColor="#2DD4BF" />
    </Sequence>

    {/* Summary label */}
    <Sequence from={660}>
      <FadeIn duration={20}>
        <Text text="Same system. 5-10× more fits."
          font="Inter" size={16} weight={700} color="#E2E8F0"
          x={960} y={950} align="center" />
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
    "header": "AGENTIC PATCHING",
    "headerColor": "#EF4444",
    "content": "dense_code_with_highlights",
    "tokenCount": 15000,
    "relevance": "~40%",
    "thematicRole": "wasteful_context"
  },
  "rightPanel": {
    "header": "PDD REGENERATION",
    "headerColor": "#2DD4BF",
    "content": "prompt_test_grounding",
    "tokenCount": 2300,
    "relevance": "100%",
    "thematicRole": "curated_context"
  },
  "compressionAnimation": {
    "codeBlocks": 20,
    "promptBlocks": 20,
    "ratio": "5-10×"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_029", "part1_economics_030"]
}
```

---
