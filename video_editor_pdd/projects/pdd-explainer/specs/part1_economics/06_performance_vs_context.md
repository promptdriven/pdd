[Remotion]

# Section 1.6: Performance vs Context — EMNLP Degradation Graph

**Tool:** Remotion
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 3:32 - 3:56

## Visual Description

A small but devastating inset graph that appears as a companion to the context window shrink visualization. The chart shows "Performance vs. Context Length" — a single line that drops steadily from left to right. This is the empirical data backing the visual metaphor.

The graph is clean, minimal, scientific. A single descending line from high performance at low context length to degraded performance at high context length. The annotation is stark: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)."

After the performance graph, we return to the main code cost chart. The "Context Rot" layer in the debt area pulses ominously. A feedback annotation appears: "Faster patching → faster growth → faster rot."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Inset graph area: 600×350px, positioned at (960, 480), centered

### Chart/Visual Elements

#### Inset Graph Frame
- Rounded rect: 600×350px, `#111827` fill, `#334155` border at 0.3, rounded 8px
- Subtle shadow: `#000000` at 0.3, 4px offset, 12px blur

#### Graph Axes
- X-axis: "Context Length (tokens)" — 0 to 128k
  - Labels: "4k", "16k", "32k", "64k", "128k"
  - Color: `#475569` at 0.5, Inter 10px
- Y-axis: "Relative Performance" — 0% to 100%
  - Labels: "0%", "25%", "50%", "75%", "100%"
  - Color: `#475569` at 0.5, Inter 10px

#### Performance Line
- Color: `#EF4444`, 2px solid
- Data: (4k, 95%), (16k, 82%), (32k, 65%), (64k, 40%), (128k, 15%)
- Smooth bezier through points
- Area under the line: `#EF4444` at 0.05

#### Annotation
- "Even with perfect retrieval, performance degrades 14-85% as context grows"
  - Inter, 12px, `#E2E8F0` at 0.6
  - Positioned below graph
- "(EMNLP, 2025)" — Inter, 10px, `#94A3B8` at 0.4

### Animation Sequence
1. **Frame 0-30 (0-1s):** Inset graph frame fades in. Dark panel appears.
2. **Frame 30-60 (1-2s):** Axes appear. Labels tick in.
3. **Frame 60-240 (2-8s):** Performance line draws from left to right. Steady decline visible.
4. **Frame 240-360 (8-12s):** Area under the line fills. The gap from 100% is dramatic.
5. **Frame 360-480 (12-16s):** Annotation text appears below the graph.
6. **Frame 480-720 (16-24s):** Graph remains. Then transitions: graph shrinks and moves to corner, main chart returns with Context Rot layer pulsing.

### Typography
- Graph title: Inter, 14px, bold (700), `#E2E8F0`
- Axis labels: Inter, 10px, `#475569` at 0.5
- Annotation: Inter, 12px, `#E2E8F0` at 0.6
- Citation: Inter, 10px, `#94A3B8` at 0.4

### Easing
- Frame appear: `easeOut(cubic)` over 20 frames
- Line draw: `easeInOut(cubic)` over 180 frames
- Area fill: `easeOut(quad)` over 60 frames
- Annotation: `easeOut(quad)` over 20 frames
- Graph shrink transition: `easeInOut(cubic)` over 30 frames

## Narration Sync
> "it gets worse. A 2025 study found that even with perfect retrieval — even if you could magically select only the right code — model performance still degrades 14 to 85% as context length grows. The window isn't just smaller. It's noisier."
> "is why AI-assisted patching shows such wildly different results across different studies."

Segments: `part1_economics_021`, `part1_economics_022`

- **212.32s** ("it gets worse"): Inset graph frame appears
- **220s** ("even with perfect retrieval"): Performance line drawing, declining
- **236s** ("14 to 85%"): Annotation appears with percentage
- **244.24s** ("is why AI-assisted patching"): Transition back to main chart

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Inset graph frame */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <InsetPanel x={960} y={480} width={600} height={350}
          bg="#111827" border="#334155" borderOpacity={0.3}
          cornerRadius={8} shadow={{ color: "#000", opacity: 0.3, blur: 12 }} />
      </FadeIn>
    </Sequence>

    {/* Graph axes */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <ChartAxes
          xRange={[0, 128000]} yRange={[0, 100]}
          xLabel="Context Length (tokens)"
          yLabel="Relative Performance"
          xTicks={["4k", "16k", "32k", "64k", "128k"]}
          yTicks={["0%", "25%", "50%", "75%", "100%"]}
          gridColor="#1E293B" axisColor="#334155"
          labelColor="#475569" labelOpacity={0.5} labelSize={10}
          region={{ x: 360, y: 305, width: 520, height: 280 }} />
      </FadeIn>
    </Sequence>

    {/* Performance degradation line */}
    <Sequence from={60}>
      <AnimatedLine
        data={[[4000, 95], [16000, 82], [32000, 65], [64000, 40], [128000, 15]]}
        color="#EF4444" strokeWidth={2}
        drawDuration={180} easing="easeInOutCubic"
        areaFill={{ color: "#EF4444", opacity: 0.05, startFrame: 180 }} />
    </Sequence>

    {/* Title */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <Text text="Performance vs. Context Length" font="Inter" size={14}
          weight={700} color="#E2E8F0"
          x={960} y={280} align="center" />
      </FadeIn>
    </Sequence>

    {/* Annotation */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text
          text="Even with perfect retrieval, performance degrades 14-85% as context grows"
          font="Inter" size={12} color="#E2E8F0" opacity={0.6}
          x={960} y={680} align="center" />
        <Text text="(EMNLP, 2025)" font="Inter" size={10}
          color="#94A3B8" opacity={0.4}
          x={960} y={700} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "inset_line_chart",
  "title": "Performance vs. Context Length",
  "xAxis": { "label": "Context Length (tokens)", "range": [0, 128000] },
  "yAxis": { "label": "Relative Performance", "range": [0, 100], "unit": "%" },
  "series": [
    {
      "id": "performance_degradation",
      "label": "Model Performance",
      "color": "#EF4444",
      "data": [[4000, 95], [16000, 82], [32000, 65], [64000, 40], [128000, 15]]
    }
  ],
  "citation": "EMNLP, 2025",
  "keyFinding": "14-85% performance degradation as context grows",
  "narrationSegments": ["part1_economics_021", "part1_economics_022"]
}
```

---
