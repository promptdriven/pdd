[Remotion]

# Section 1.6: Performance vs Context Length — The EMNLP Evidence

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 3:08 - 3:26

## Visual Description

A subtle graph inset appears overlaying the context window visualization. The graph shows "Performance vs. Context Length" — a steadily dropping line proving that even with perfect retrieval, model performance degrades as input length grows. This is the EMNLP 2025 finding.

The graph is compact and clinical — positioned in the lower-right as a supporting evidence callout. The line drops from high-left to low-right with a shaded area beneath showing the degradation range (14-85%). A label cites the source. After the main point lands, a second annotation fades in about context rot: "Faster patching → faster growth → faster rot" — a causal chain.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (inherited from context window visualization)
- Inset graph area: 420×280px, positioned at (1350, 720), with `#0F172A` at 0.9 background, 1px border `#1E293B`

### Chart/Visual Elements

#### Inset Graph
- X-axis: "Context Length" — Inter, 9px, `#64748B` at 0.4
- Y-axis: "Model Performance" — Inter, 9px, `#64748B` at 0.4
- Grid: 4×3 light grid, `#1E293B` at 0.05
- Axis lines: `#334155` at 0.3, 1px

#### Performance Line
- Color: `#EF4444`, 2px solid stroke
- Path: descending curve from (left, 90%) to (right, 15%) — steeper in the middle
- Glow: 4px Gaussian blur, `#EF4444` at 0.1
- Shaded area below line: `#EF4444` at 0.04

#### Degradation Range Label
- "14-85% degradation" — Inter, 11px, bold, `#EF4444` at 0.7
- Positioned centered in the shaded area

#### Source Citation
- "Even with perfect retrieval, performance degrades 14-85% as context grows" — Inter, 9px, `#94A3B8` at 0.4
- "(EMNLP, 2025)" — Inter, 9px, `#64748B` at 0.3

#### Context Rot Annotation (appears after inset)
- Position: centered, large — (960, 200)
- "Faster patching → faster growth → faster rot" — Inter, 16px, semi-bold (600), `#EF4444` at 0.7
- Arrows rendered as animated connecting symbols
- Subtle red pulse on "rot"

### Animation Sequence
1. **Frame 0-30 (0-1s):** Context window visualization still visible in background. Inset graph container slides in from lower-right.
2. **Frame 30-60 (1-2s):** Axes draw inside inset. Grid appears.
3. **Frame 60-180 (2-6s):** Performance line draws left-to-right, descending steadily. Shaded area fills beneath.
4. **Frame 180-240 (6-8s):** "14-85% degradation" label fades in centered in the shaded area. Source citation appears below inset.
5. **Frame 240-360 (8-12s):** Hold on inset. The evidence sinks in.
6. **Frame 360-420 (12-14s):** Inset dims to 0.3 opacity. Context rot annotation types in at center: "Faster patching → faster growth → faster rot" with each arrow animating.
7. **Frame 420-540 (14-18s):** "rot" pulses red. Hold on the causal chain.

### Typography
- Inset axis labels: Inter, 9px, `#64748B` at 0.4
- Degradation label: Inter, 11px, bold, `#EF4444` at 0.7
- Source: Inter, 9px, `#94A3B8` at 0.4
- Context rot annotation: Inter, 16px, semi-bold (600), `#EF4444` at 0.7

### Easing
- Inset slide-in: `easeOut(cubic)` over 30 frames
- Line draw: `easeInOut(quad)` over 120 frames
- Shaded area fill: `easeOut(quad)` over 60 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Arrow animate: `easeOut(cubic)` over 15 frames each, staggered
- Rot pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "And it gets worse. A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades—fourteen to eighty-five percent."
> "This is why AI-assisted patching is really two stories."

Segments: `part1_economics_021`, `part1_economics_022`

- **3:08** ("it gets worse"): Inset graph slides in
- **3:20** ("fourteen to eighty-five percent"): Degradation label appears
- **3:26** ("two stories"): Context rot annotation types in

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Background: context window viz at low opacity */}
    <Opacity value={0.3}>
      <ContextWindowVisualization />
    </Opacity>

    {/* Inset graph */}
    <Sequence from={0}>
      <SlideIn from="right" distance={30} duration={30}>
        <InsetGraph position={[1350, 720]} width={420} height={280}
          background="#0F172A" backgroundOpacity={0.9}
          borderColor="#1E293B">
          <AnimatedAxis axis="x" label="Context Length" />
          <AnimatedAxis axis="y" label="Model Performance" />

          <Sequence from={60}>
            <AnimatedLine data={perfDegradationData}
              color="#EF4444" width={2}
              glow={{ blur: 4, opacity: 0.1 }}
              fillBelow={{ color: '#EF4444', opacity: 0.04 }}
              drawDuration={120} />
          </Sequence>

          <Sequence from={180}>
            <FadeIn duration={20}>
              <Text text="14-85% degradation"
                font="Inter" size={11} weight={700}
                color="#EF4444" opacity={0.7}
                align="center" />
            </FadeIn>
          </Sequence>
        </InsetGraph>
      </SlideIn>
    </Sequence>

    {/* Source citation */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <Text text="Even with perfect retrieval, performance degrades (EMNLP, 2025)"
          font="Inter" size={9} color="#94A3B8" opacity={0.4}
          x={1350} y={880} align="center" />
      </FadeIn>
    </Sequence>

    {/* Context rot annotation */}
    <Sequence from={360}>
      <CausalChain
        items={["Faster patching", "faster growth", "faster rot"]}
        separator="→"
        font="Inter" size={16} weight={600}
        color="#EF4444" opacity={0.7}
        x={960} y={200} stagger={15}
        pulseItem={2} pulseColor="#EF4444" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "inset_chart",
  "chartId": "performance_vs_context",
  "chartType": "single_line_degradation",
  "xAxis": { "label": "Context Length" },
  "yAxis": { "label": "Model Performance" },
  "series": [
    {
      "id": "performance_degradation",
      "color": "#EF4444",
      "degradationRange": { "min": 14, "max": 85 },
      "source": "EMNLP, 2025"
    }
  ],
  "causalChain": ["Faster patching", "faster growth", "faster rot"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_021", "part1_economics_022"]
}
```

---
