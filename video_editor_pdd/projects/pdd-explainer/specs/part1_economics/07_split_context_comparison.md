[split:]

# Section 1.6: Split Context Comparison — Agentic Patching vs PDD Regeneration

**Tool:** Split
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 4:52 - 5:12

## Visual Description

A vertical split screen comparison that visualizes the key difference in context window usage between agentic patching (LEFT) and PDD regeneration (RIGHT).

**LEFT panel — "Agentic patching":** A context window filled with 15,000 tokens of raw code. The window is dense, packed, overwhelming. Red highlights mark irrelevant sections that the retrieval system grabbed. A tiny green section shows the actually relevant code, buried in noise. The window looks like it's straining under the load. A small label reads: "15,000 tokens • ~60% irrelevant".

**RIGHT panel — "PDD regeneration":** The same-sized context window with a 300-token prompt in clean natural language, 2,000 tokens of tests below it, and a small grounding example. The window is clean, focused, with generous whitespace. Room to breathe. A label reads: "2,300 tokens • 100% author-curated".

The visual contrast is immediate: LEFT is chaos and waste, RIGHT is clarity and focus. Neither panel is animated heavily — the static comparison does the work.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.12

### Chart/Visual Elements

#### Panel Headers
- LEFT: "Agentic Patching" — Inter, 14px, semi-bold (600), `#D9944A` at 0.6, letter-spacing 2px, centered at y: 50
- RIGHT: "PDD Regeneration" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.6, letter-spacing 2px, centered at y: 50

#### Left Panel — Context Window (Code-Filled)
- Context window border: rounded rect, `#D9944A` 1px at 0.3, fills most of panel (80px padding)
- Interior: dense code blocks — JetBrains Mono, 8px, `#94A3B8` at 0.35
- Red highlighted regions: 4-5 blocks, `#E74C3C` at 0.08 background, `#E74C3C` 1px border at 0.2
  - Small "irrelevant" labels: Inter, 7px, `#E74C3C` at 0.4
- Green highlighted region: 1 small block (~8% of window), `#5AAA6E` at 0.10 background, `#5AAA6E` 1px border at 0.3
  - Small "relevant" label: Inter, 7px, `#5AAA6E` at 0.5
- Token count: "15,000 tokens" — Inter, 11px, `#D9944A` at 0.5, bottom of window
- Quality note: "~60% irrelevant" — Inter, 10px, `#E74C3C` at 0.4, below token count
- Fill indicator bar: thin bar at bottom of window, `#E74C3C` at 0.2 filling 100% (overloaded)

#### Right Panel — Context Window (Prompt-Filled)
- Context window border: same size rounded rect, `#4A90D9` 1px at 0.3
- Interior sections:
  - **Prompt block:** clean natural language text, Inter 10px, `#E2E8F0` at 0.6, ~15 lines, with `#4A90D9` left border 3px (blockquote style). Label: "prompt" — Inter, 8px, `#4A90D9` at 0.4
  - **Tests block:** organized test names, JetBrains Mono 8px, `#5AAA6E` at 0.5, with green left border. Label: "tests" — Inter, 8px, `#5AAA6E` at 0.4
  - **Grounding block:** small code example, JetBrains Mono 8px, `#94A3B8` at 0.3, with muted left border. Label: "grounding" — Inter, 8px, `#94A3B8` at 0.3
  - **Whitespace:** generous empty space below — the window is ~30% empty
- Token count: "2,300 tokens" — Inter, 11px, `#4A90D9` at 0.5, bottom of window
- Quality note: "100% author-curated" — Inter, 10px, `#5AAA6E` at 0.5, below token count
- Fill indicator bar: thin bar at bottom, `#4A90D9` at 0.2 filling ~25% (lots of room)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous visualization fades out. Split line appears.
2. **Frame 30-60 (1-2s):** Panel headers fade in simultaneously.
3. **Frame 60-150 (2-5s):** LEFT: code fills the context window rapidly — blocks appear, pack tight, overflow feeling. RED highlights appear staggered.
4. **Frame 150-240 (5-8s):** RIGHT: prompt block fades in cleanly with blue border. Tests block appears below. Grounding appears. Whitespace is visible.
5. **Frame 240-300 (8-10s):** Token counts appear on both sides simultaneously. Quality notes fade in.
6. **Frame 300-360 (10-12s):** Fill indicator bars animate. LEFT fills to 100% (red). RIGHT fills to ~25% (blue).
7. **Frame 360-600 (12-20s):** Hold. The contrast speaks for itself. LEFT panel red highlights pulse faintly (noise). RIGHT panel sits clean and still.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- Code text: JetBrains Mono, 8px, `#94A3B8` at 0.35
- Prompt text: Inter, 10px, `#E2E8F0` at 0.6
- Section labels: Inter, 8px, respective colors
- Token counts: Inter, 11px, respective panel colors at 0.5
- Quality notes: Inter, 10px, respective colors

### Easing
- Panel header fade: `easeOut(quad)` over 15 frames
- Code block fill: `easeOut(cubic)` staggered over 60 frames (rapid, chaotic feeling)
- Prompt section fade: `easeOut(quad)` over 20 frames each (calm, orderly)
- Token count fade: `easeOut(quad)` over 15 frames
- Fill bar animate: `easeOut(cubic)` over 20 frames
- Red highlight pulse: `easeInOut(sine)` on 50-frame cycle, opacity 0.08 → 0.12

## Narration Sync
> "And there's something else. These models are trained on up to thirty times more natural language than code. Natural language is their deepest fluency. MIT showed that giving models natural language context for coding tasks improved performance by up to eighty-nine percent. A prompt is natural language. You're speaking the model's strongest language and giving it room to think."

Segments: `part1_economics_024`, `part1_economics_025`

- **4:52** ("there's something else"): Split screen appears
- **4:55** ("thirty times more natural language"): LEFT fills with code, RIGHT shows clean prompt
- **5:02** ("eighty-nine percent"): Both panels fully visible, contrast stark
- **5:06** ("room to think"): RIGHT panel whitespace is prominent

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Agentic Patching */}
    <Panel x={0} width={958}>
      <PanelHeader text="AGENTIC PATCHING"
        color="#D9944A" opacity={0.6} letterSpacing={2} y={50} />

      <Sequence from={60}>
        <ContextWindowFrame borderColor="#D9944A">
          <DenseCodeFill lines={200} font="JetBrains Mono" size={8}
            color="#94A3B8" opacity={0.35} fillDuration={60} />
          <RedHighlights count={5} color="#E74C3C"
            opacity={0.08} stagger={10} />
          <GreenHighlight size={0.08} color="#5AAA6E"
            opacity={0.10} label="relevant" />
        </ContextWindowFrame>
      </Sequence>

      <Sequence from={240}>
        <TokenCount value="15,000 tokens" color="#D9944A" />
        <QualityNote text="~60% irrelevant" color="#E74C3C" />
        <FillBar percent={100} color="#E74C3C" />
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.12} />

    {/* Right panel — PDD Regeneration */}
    <Panel x={962} width={958}>
      <PanelHeader text="PDD REGENERATION"
        color="#4A90D9" opacity={0.6} letterSpacing={2} y={50} />

      <Sequence from={150}>
        <ContextWindowFrame borderColor="#4A90D9">
          <PromptBlock lines={15} borderColor="#4A90D9"
            font="Inter" size={10} color="#E2E8F0" />
          <TestsBlock lines={12} borderColor="#5AAA6E"
            font="JetBrains Mono" size={8} color="#5AAA6E" />
          <GroundingBlock lines={6} borderColor="#94A3B8"
            font="JetBrains Mono" size={8} color="#94A3B8" />
          {/* Remaining ~30% is whitespace */}
        </ContextWindowFrame>
      </Sequence>

      <Sequence from={240}>
        <TokenCount value="2,300 tokens" color="#4A90D9" />
        <QualityNote text="100% author-curated" color="#5AAA6E" />
        <FillBar percent={25} color="#4A90D9" />
      </Sequence>
    </Panel>
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
    "label": "Agentic Patching",
    "labelColor": "#D9944A",
    "content": "dense_code_context_window",
    "tokenCount": 15000,
    "irrelevantPercent": 60,
    "fillPercent": 100,
    "highlights": {
      "irrelevant": { "count": 5, "color": "#E74C3C" },
      "relevant": { "percent": 8, "color": "#5AAA6E" }
    }
  },
  "rightPanel": {
    "label": "PDD Regeneration",
    "labelColor": "#4A90D9",
    "content": "prompt_context_window",
    "tokenCount": 2300,
    "sections": [
      { "type": "prompt", "lines": 15, "color": "#4A90D9" },
      { "type": "tests", "lines": 12, "color": "#5AAA6E" },
      { "type": "grounding", "lines": 6, "color": "#94A3B8" }
    ],
    "fillPercent": 25,
    "qualityNote": "100% author-curated"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part1_economics_024", "part1_economics_025"]
}
```

---
