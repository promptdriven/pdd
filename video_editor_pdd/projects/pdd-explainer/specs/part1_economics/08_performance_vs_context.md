[Remotion]

# Section 1.8: Performance vs. Context Length — EMNLP Study Inset

**Tool:** Remotion
**Duration:** ~49s (1470 frames @ 30fps)
**Timestamp:** 3:44 - 4:33

## Visual Description

A subtle inset graph appears in the lower-right corner while the context window grid holds in the background (dimmed). The inset shows a single declining line: "Performance vs. Context Length."

The line drops steadily from left to right — demonstrating that even with perfect retrieval, model performance degrades as context grows. A label reads: "Even with perfect retrieval, performance degrades 14-85% as context grows (EMNLP, 2025)."

After the inset holds, the view returns to the main chart. The "Context Rot" layer from the debt area pulses with a new annotation: "Faster patching → faster growth → faster rot."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Context grid from spec 07 dimmed to 30% opacity in background

### Chart/Visual Elements

#### Inset Graph
- Size: 480×300px, positioned at (1350, 680) — lower-right
- Border: `#334155` 1px, 8px corner radius
- Background: `#0F172A` at 0.95 (slightly lighter than main background)
- Title: "Performance vs. Context Length" — Inter 14px, bold (600), `#E2E8F0`

#### Inset Line
- Single declining line: `#EF4444`, 2.5px
- X-axis: "Context length (tokens)" — labeled at 4K, 32K, 128K, 1M
- Y-axis: "Model Performance" — 100% to 15%
- Line drops: 100% at 4K → 86% at 32K → 50% at 128K → 15% at 1M

#### Inset Label
- "14-85% degradation" — Inter 12px, `#EF4444` at 0.8
- "(EMNLP, 2025)" — Inter 11px, `#94A3B8`

#### Context Rot Pulse (after return to chart)
- The "Context Rot" layer from debt area pulses
- New annotation: "Faster patching → faster growth → faster rot" — Inter 14px, italic, `#F59E0B`

### Animation Sequence
1. **Frame 0-60 (0-2s):** Context grid dims to 30%. Inset border draws in lower-right.
2. **Frame 60-90 (2-3s):** Inset background fills. Title types in.
3. **Frame 90-210 (3-7s):** Inset axes draw. Line draws from left to right — steady decline.
4. **Frame 210-360 (7-12s):** Hold on inset. Labels appear.
5. **Frame 360-600 (12-20s):** Hold. Narration covers EMNLP study, Chroma study, context rot naming.
6. **Frame 600-720 (20-24s):** Inset fades out. View transitions back to code cost chart with debt area visible.
7. **Frame 720-900 (24-30s):** Context Rot layer pulses. "Faster patching → faster growth → faster rot" annotation appears.
8. **Frame 900-1470 (30-49s):** Hold. Chart with pulsing debt area.

### Typography
- Inset title: Inter, 14px, semi-bold (600), `#E2E8F0`
- Inset axis labels: Inter, 11px, regular (400), `#94A3B8`
- Degradation label: Inter, 12px, regular (400), `#EF4444` at 0.8
- Cycle annotation: Inter, 14px, italic, `#F59E0B`

### Easing
- Inset border draw: `easeOut(quad)` over 30 frames
- Line draw: `easeInOut(cubic)` over 120 frames
- Inset fade-out: `easeIn(quad)` over 60 frames
- Context Rot pulse: `easeInOut(sine)` on 45-frame cycle
- Annotation fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "And it gets worse. A 2025 EMNLP study proved that even when the model retrieves the right information, performance still degrades — 14 to 85 percent — just from the sheer length of the input."
> "This is why AI-assisted patching is really two stories — and why every productivity study seems to contradict every other one."

Segments: `part1_economics_017`, `part1_economics_018`

- **223.60s** (seg 017): Inset appears — "And it gets worse"
- **240.0s**: Line fully drawn, labels visible
- **268.56s** (seg 017 ends): Inset holds
- **268.76s** (seg 018): Transition back to chart — "This is why AI-assisted patching is really two stories"
- **277.54s** (seg 018 ends): Pulsing debt area with cycle annotation

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1470}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Dimmed context grid background */}
    <Opacity value={0.3}>
      <CodeBlockGrid gridSize={32} />
    </Opacity>

    {/* Inset graph */}
    <Sequence from={0} durationInFrames={720}>
      <InsetChart
        position={{ x: 1350, y: 680 }}
        width={480} height={300}
        borderColor="#334155"
        backgroundColor="#0F172A"
        title="Performance vs. Context Length"
      >
        <AnimatedLine
          data={performanceData}
          color="#EF4444" strokeWidth={2.5}
          drawDuration={120}
        />
        <Sequence from={210}>
          <FadeIn duration={20}>
            <Text text="14-85% degradation" color="#EF4444"
              size={12} opacity={0.8} />
            <Text text="(EMNLP, 2025)" color="#94A3B8" size={11} />
          </FadeIn>
        </Sequence>
      </InsetChart>
    </Sequence>

    {/* Return to chart with context rot pulse */}
    <Sequence from={720}>
      <DebtAreaWithPulse layer="context_rot"
        pulseColor="#F59E0B" cycleFrames={45} />
      <Sequence from={90}>
        <FadeIn duration={20}>
          <Text text="Faster patching → faster growth → faster rot"
            font="Inter" size={14} style="italic"
            color="#F59E0B" />
        </FadeIn>
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "inset_chart",
  "chartId": "performance_vs_context_length",
  "insetPosition": { "x": 1350, "y": 680 },
  "insetSize": { "width": 480, "height": 300 },
  "series": [
    {
      "id": "performance_degradation",
      "color": "#EF4444",
      "data": [
        { "x": "4K", "y": 1.0 },
        { "x": "32K", "y": 0.86 },
        { "x": "128K", "y": 0.50 },
        { "x": "1M", "y": 0.15 }
      ]
    }
  ],
  "annotations": [
    { "text": "14-85% degradation", "source": "EMNLP, 2025" },
    { "text": "Faster patching → faster growth → faster rot", "type": "cycle" }
  ],
  "narrationSegments": ["part1_economics_017", "part1_economics_018"]
}
```

---
