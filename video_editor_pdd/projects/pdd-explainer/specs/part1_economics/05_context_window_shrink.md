[Remotion]

# Section 1.4: Context Window Shrink — The AI Blindspot

**Tool:** Remotion
**Duration:** ~30s (900 frames @ 30fps)
**Timestamp:** 3:57 - 4:27

## Visual Description

The chart dissolves and is replaced by a new spatial visualization. A glowing rectangular "context window" appears over a small codebase represented as a 4x4 grid of code blocks. The window covers most of the grid (~80%). This looks good — AI can see almost everything.

Then the codebase grid grows in stages: 4x4 → 8x8 → 16x16 → 32x32. The context window stays THE SAME SIZE. A counter animates: "Context coverage: 80% → 40% → 10% → 2%". The window becomes a tiny rectangle over a massive grid.

Inside the tiny window, some blocks highlight red (irrelevant code the AI grabbed). Outside the window, green blocks highlight (the code that was actually needed but couldn't be seen). This creates a visceral sense of the AI's blindspot growing.

A small inset graph appears in the lower-right: "Performance vs. Context Length" showing a line that drops steadily, labeled with the EMNLP 2025 citation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Grid area: centered, 800x800 at maximum extent
- Inset graph: 320x200, positioned at bottom-right (1540, 820)

### Chart/Visual Elements

#### Codebase Grid
- Initial: 4x4 grid of 120x120px blocks, 8px gap
- Each block: rounded rect, `#1A2332` fill, `#334155` 1px border at 0.3
- Block content: 3-4 lines of faux code, JetBrains Mono 6px, `#94A3B8` at 0.15
- Growth stages: 4x4 → 8x8 → 16x16 → 32x32 (blocks shrink to maintain overall size)

#### Context Window Overlay
- Glowing rectangle: `#4A90D9` 2px border at 0.6, with 8px outer glow `#4A90D9` at 0.12
- Interior tint: `#4A90D9` at 0.04
- SIZE STAYS FIXED throughout all grid stages (approximately 480x480px area)

#### Coverage Counter
- Position: top-right (1580, 100)
- "Context coverage:" — Inter, 12px, `#94A3B8` at 0.5
- Percentage: Inter, 28px, bold, animated color transition:
  - 80%: `#5AAA6E` (green — healthy)
  - 40%: `#D9C44A` (yellow — concerning)
  - 10%: `#D9944A` (amber — problematic)
  - 2%: `#E74C3C` (red — critical)

#### Red Highlight Blocks (Inside Window — Irrelevant)
- 3-4 blocks inside the window highlighted: `#E74C3C` at 0.15, red border at 0.3
- Small "✗" icon at corner

#### Green Highlight Blocks (Outside Window — Needed)
- 5-6 blocks outside the window highlighted: `#5AAA6E` at 0.15, green border at 0.3
- Small "✓" icon at corner
- Subtle pulsing glow — calling for attention but unreachable

#### Inset Performance Graph
- Mini chart: "Performance vs. Context Length"
- X-axis: context length (tokens), unlabeled but implied
- Y-axis: performance (0-100%)
- Single declining line: `#E74C3C`, 2px
- Citation: "EMNLP, 2025" — Inter, 8px, `#94A3B8` at 0.3
- Range label: "−14% to −85%" — Inter, 10px, `#E74C3C` at 0.6
- Border: `#334155` at 0.15, rounded

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous chart fades out. Dark background.
2. **Frame 30-90 (1-3s):** 4x4 grid fades in. Context window overlay appears. Counter: "80%". Window covers most of the grid. Warm, capable feeling.
3. **Frame 90-180 (3-6s):** Grid morphs to 8x8 — blocks shrink and multiply. Context window stays fixed. Counter animates to "40%". Coverage visibly reduced.
4. **Frame 180-270 (6-9s):** Grid morphs to 16x16. Counter: "10%". Window is now a small rectangle in a large grid.
5. **Frame 270-360 (9-12s):** Grid morphs to 32x32. Counter: "2%" in red. Window is tiny. The grid fills the frame.
6. **Frame 360-480 (12-16s):** Red highlights appear inside window (irrelevant code). Green highlights appear outside window (needed code). The AI's blindspot is visceral.
7. **Frame 480-600 (16-20s):** Inset performance graph draws in the lower-right. Line drops. "−14% to −85%" label appears.
8. **Frame 600-900 (20-30s):** Hold for narration. Context window pulses faintly. Green blocks outside pulse with unreachable urgency.

### Typography
- Coverage counter label: Inter, 12px, `#94A3B8` at 0.5
- Coverage percentage: Inter, 28px, bold, color-animated
- Block faux code: JetBrains Mono, 6px, `#94A3B8` at 0.15
- Inset graph title: Inter, 10px, bold, `#E2E8F0` at 0.5
- Inset citation: Inter, 8px, `#94A3B8` at 0.3

### Easing
- Grid growth morphs: `easeInOut(cubic)` over 40 frames each
- Counter number change: `easeOut(quad)` over 15 frames (interpolated)
- Counter color change: `easeInOut(quad)` over 20 frames
- Red/green highlights: `easeOut(quad)` staggered fade-in, 5 frames apart
- Inset graph draw: `linear` line draw over 30 frames
- Green block pulse: `easeInOut(sine)` on 45-frame cycle, glow opacity 0.15 → 0.25 → 0.15

## Narration Sync
> "When your codebase is small, AI tools are brilliant. The context window — what the model can actually see — covers almost everything."
> "But codebases grow. And that window? It stays the same size. A typical enterprise codebase spans millions of tokens. Even the largest context windows hold a fraction of that."
> "So now the AI has to guess what's relevant. Tools like Cursor use embeddings. Claude Code uses agentic search — grep, file by file."
> "And it gets worse. A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades — fourteen to eighty-five percent."

Segments: `part1_economics_017`, `part1_economics_018`, `part1_economics_019`, `part1_economics_020`

- **3:57** ("codebase is small"): 4x4 grid appears, context window covers 80%
- **4:03** ("codebases grow"): Grid expands through 8x8, 16x16, 32x32
- **4:10** ("AI has to guess"): Red/green highlights appear — wrong code inside, right code outside
- **4:18** ("EMNLP study"): Inset performance graph draws in

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={900}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Codebase grid with morphing stages */}
    <Sequence from={30}>
      <CodebaseGrid
        stages={[
          { frame: 0, gridSize: 4, coverage: 0.80 },
          { frame: 60, gridSize: 8, coverage: 0.40 },
          { frame: 150, gridSize: 16, coverage: 0.10 },
          { frame: 240, gridSize: 32, coverage: 0.02 }
        ]}
        blockColor="#1A2332"
        blockBorder="#334155"
        morphDuration={40}
      />
    </Sequence>

    {/* Fixed-size context window overlay */}
    <Sequence from={30}>
      <ContextWindow
        width={480} height={480}
        borderColor="#4A90D9" borderWidth={2}
        glowColor="#4A90D9" glowRadius={8} glowOpacity={0.12}
        tintColor="#4A90D9" tintOpacity={0.04}
      />
    </Sequence>

    {/* Coverage counter */}
    <Sequence from={30}>
      <CoverageCounter
        stages={[
          { value: 80, color: "#5AAA6E" },
          { value: 40, color: "#D9C44A" },
          { value: 10, color: "#D9944A" },
          { value: 2, color: "#E74C3C" }
        ]}
        x={1580} y={100}
      />
    </Sequence>

    {/* Red/green highlights */}
    <Sequence from={360}>
      <BlockHighlights
        inside={{ color: "#E74C3C", count: 4, icon: "✗" }}
        outside={{ color: "#5AAA6E", count: 6, icon: "✓" }}
        staggerDelay={5}
      />
    </Sequence>

    {/* Inset performance graph */}
    <Sequence from={480}>
      <InsetGraph
        title="Performance vs. Context Length"
        data={performanceDecline}
        lineColor="#E74C3C"
        citation="EMNLP, 2025"
        rangeLabel="−14% to −85%"
        x={1540} y={820} width={320} height={200}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "spatial_visualization",
  "chartType": "context_window_shrink",
  "gridStages": [
    { "size": 4, "coverage": 0.80, "coverageColor": "#5AAA6E" },
    { "size": 8, "coverage": 0.40, "coverageColor": "#D9C44A" },
    { "size": 16, "coverage": 0.10, "coverageColor": "#D9944A" },
    { "size": 32, "coverage": 0.02, "coverageColor": "#E74C3C" }
  ],
  "contextWindow": {
    "fixedSize": { "width": 480, "height": 480 },
    "borderColor": "#4A90D9",
    "glowColor": "#4A90D9"
  },
  "highlights": {
    "irrelevantInsideWindow": { "count": 4, "color": "#E74C3C" },
    "neededOutsideWindow": { "count": 6, "color": "#5AAA6E" }
  },
  "insetGraph": {
    "title": "Performance vs. Context Length",
    "citation": "EMNLP, 2025",
    "degradationRange": "14% to 85%",
    "lineColor": "#E74C3C"
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": [
    "part1_economics_017", "part1_economics_018",
    "part1_economics_019", "part1_economics_020"
  ]
}
```

---
