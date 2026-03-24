[split:]

# Section 1.9: Agentic Patching vs PDD Regeneration — Side-by-Side

**Tool:** Split
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 4:28 - 4:50

## Visual Description

A vertical split screen comparing the two approaches to code maintenance. LEFT panel: "Agentic Patching" — a context window visualization crammed with 15,000 tokens of code. Red highlights mark irrelevant sections the AI grabbed. A tiny green section shows the actually relevant code buried in the noise. RIGHT panel: "PDD Regeneration" — a context window with a clean 300-token prompt, 2,000 tokens of tests, and a small grounding example. Clean. Focused. Room to think.

The contrast is stark. The left panel feels cluttered and anxious. The right panel feels spacious and intentional. Both panels use a code-editor aesthetic with syntax-highlighted token blocks.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.2

### Chart/Visual Elements

#### Panel Headers
- LEFT: "AGENTIC PATCHING" — Inter, 14px, semi-bold (600), `#EF4444` at 0.4, letter-spacing 2px, centered at y: 40
- RIGHT: "PDD REGENERATION" — Inter, 14px, semi-bold (600), `#4ADE80` at 0.4, letter-spacing 2px, centered at y: 40

#### Left Panel — Agentic Patching (x: 0 to x: 958)
- Background: `#0A0F1A`
- Context window box: 400×500px, centered in panel, border `#334155` at 0.3
- Token counter: "~15,000 tokens" — JetBrains Mono, 10px, `#EF4444` at 0.5, top-right of box
- Inside box: dense rows of code blocks (faux syntax-highlighted)
  - Irrelevant blocks: `#EF4444` at 0.15 background, 12-15 blocks filling ~80% of space
  - Relevant blocks: `#4ADE80` at 0.15 background, 2-3 tiny blocks (~5% of space)
- Label below box: "Red = irrelevant code retrieved" — Inter, 9px, `#EF4444` at 0.4
- Second label: "Green = actually needed" — Inter, 9px, `#4ADE80` at 0.4
- Stress indicator: subtle red vignette at edges

#### Right Panel — PDD Regeneration (x: 962 to x: 1920)
- Background: `#0A0F1A`
- Context window box: 400×500px, centered in panel, border `#334155` at 0.3
- Token counter: "~2,500 tokens" — JetBrains Mono, 10px, `#4ADE80` at 0.5, top-right of box
- Inside box: clean layered sections
  - Prompt section: `#4A90D9` at 0.12 background, 60px height, label "Prompt (300 tokens)"
  - Tests section: `#D9944A` at 0.12 background, 100px height, label "Tests (2,000 tokens)"
  - Grounding section: `#5AAA6E` at 0.12 background, 40px height, label "Grounding example"
  - Remaining space: empty `#0F172A` at 0.3, label "Room to think"
- Clean indicator: subtle blue vignette at edges, calming

#### Bottom Comparison Stats
- LEFT: "Context utilization: ~5%" — Inter, 11px, `#EF4444` at 0.5
- RIGHT: "Context utilization: ~95%" — Inter, 11px, `#4ADE80` at 0.5

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-90 (0.67-3s):** Left panel: context window box draws. Dense code blocks fill in rapidly — chaotic, overwhelming. Red highlights appear on irrelevant sections.
3. **Frame 90-180 (3-6s):** Left panel: tiny green relevant blocks barely visible. Token counter: "~15,000 tokens". The mess is complete.
4. **Frame 180-300 (6-10s):** Right panel: context window box draws. Clean layered sections appear one by one — prompt (blue), tests (amber), grounding (green). Each appears neatly with gentle fade.
5. **Frame 300-360 (10-12s):** Right panel: "Room to think" label in the empty space. Token counter: "~2,500 tokens". The contrast is stark.
6. **Frame 360-420 (12-14s):** Legend labels appear below each panel.
7. **Frame 420-540 (14-18s):** Bottom comparison stats appear: "~5% utilization" vs "~95% utilization".
8. **Frame 540-660 (18-22s):** Hold on complete split. Right panel subtly pulses with blue glow.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors at 0.4, letter-spacing 2px
- Token counters: JetBrains Mono, 10px, respective colors at 0.5
- Section labels inside boxes: Inter, 9px, `#94A3B8` at 0.5
- Legend labels: Inter, 9px, respective colors at 0.4
- Comparison stats: Inter, 11px, respective colors at 0.5

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Code blocks fill: `easeOut(quad)`, staggered 1 frame each
- Clean sections appear: `easeOut(cubic)` over 20 frames, staggered 30 frames
- Stats fade: `easeOut(quad)` over 20 frames
- Right panel pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs."
> "And there's something else. These models are trained on up to thirty times more natural language than code."

Segments: `part1_economics_027`, `part1_economics_028`

- **4:28** ("Regeneration doesn't have this problem"): Split draws, left panel fills chaotically
- **4:36** ("A prompt is a fifth"): Right panel shows clean layout
- **4:42** ("something else"): Comparison stats appear
- **4:50** ("thirty times more natural language"): Hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Agentic Patching */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="AGENTIC PATCHING" color="#EF4444"
          opacity={0.4} letterSpacing={2} y={40} />

        <Sequence from={20}>
          <ContextWindowBox width={400} height={500}
            borderColor="#334155" borderOpacity={0.3}>
            <DenseCodeBlocks count={60}
              irrelevantColor="#EF4444" irrelevantOpacity={0.15}
              irrelevantCount={50}
              relevantColor="#4ADE80" relevantOpacity={0.15}
              relevantCount={3}
              fillDuration={70} stagger={1} />
            <TokenCounter value="~15,000 tokens"
              color="#EF4444" opacity={0.5} />
          </ContextWindowBox>
        </Sequence>

        <Sequence from={360}>
          <FadeIn duration={20}>
            <Text text="Red = irrelevant code retrieved"
              color="#EF4444" opacity={0.4} size={9} y={820} />
            <Text text="Green = actually needed"
              color="#4ADE80" opacity={0.4} size={9} y={840} />
          </FadeIn>
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.2} drawDuration={15} />

    {/* Right panel — PDD Regeneration */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="PDD REGENERATION" color="#4ADE80"
          opacity={0.4} letterSpacing={2} y={40} />

        <Sequence from={180}>
          <ContextWindowBox width={400} height={500}
            borderColor="#334155" borderOpacity={0.3}>
            <CleanSection label="Prompt (300 tokens)"
              color="#4A90D9" opacity={0.12} height={60}
              delay={0} />
            <CleanSection label="Tests (2,000 tokens)"
              color="#D9944A" opacity={0.12} height={100}
              delay={30} />
            <CleanSection label="Grounding example"
              color="#5AAA6E" opacity={0.12} height={40}
              delay={60} />
            <EmptySpace label="Room to think"
              color="#0F172A" opacity={0.3} delay={90} />
            <TokenCounter value="~2,500 tokens"
              color="#4ADE80" opacity={0.5} />
          </ContextWindowBox>
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Comparison stats */}
    <Sequence from={420}>
      <FadeIn duration={20}>
        <Text text="Context utilization: ~5%"
          color="#EF4444" opacity={0.5} size={11}
          x={480} y={920} align="center" />
        <Text text="Context utilization: ~95%"
          color="#4ADE80" opacity={0.5} size={11}
          x={1440} y={920} align="center" />
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
    "label": "AGENTIC PATCHING",
    "content": "context_window_cluttered",
    "tokenCount": 15000,
    "relevantPercent": 5,
    "color": "#EF4444",
    "background": "#0A0F1A"
  },
  "rightPanel": {
    "label": "PDD REGENERATION",
    "content": "context_window_clean",
    "tokenCount": 2500,
    "relevantPercent": 95,
    "sections": [
      { "label": "Prompt", "tokens": 300, "color": "#4A90D9" },
      { "label": "Tests", "tokens": 2000, "color": "#D9944A" },
      { "label": "Grounding", "tokens": 200, "color": "#5AAA6E" }
    ],
    "color": "#4ADE80",
    "background": "#0A0F1A"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part1_economics_027", "part1_economics_028"]
}
```

---
