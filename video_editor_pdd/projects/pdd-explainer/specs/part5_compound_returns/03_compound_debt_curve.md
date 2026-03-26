[Remotion]

# Section 5.3: Compound Debt Curve — Pie Chart Morphs to Exponential Growth

**Tool:** Remotion
**Duration:** ~17s (510 frames @ 30fps)
**Timestamp:** 0:24 - 0:41

## Visual Description
The pie chart from the previous shot morphs into a dramatic exponential curve. The amber maintenance wedge stretches and reshapes itself into an upward-sweeping exponential line labeled "Debt x (1 + Rate)^Time". This is the compound interest curve of technical debt — starting slow, then exploding upward.

Simultaneously, a second flat line appears: "Regeneration cost (debt resets each cycle)" — drawn in cool teal, running nearly flat along the bottom of the chart. This represents the PDD model where cost resets to near-zero each generation cycle.

The CISQ statistic "$1.52 trillion / year" appears as a callout anchored to the steep part of the curve, giving the exponential abstraction a concrete, staggering number.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal dashed at `#1E293B` opacity `0.08`, 5 lines evenly spaced on Y-axis

### Chart/Visual Elements

#### Axes
- X-axis: "Time (years)" — 0 to 10, tick marks at each year
  - Color: `#475569` opacity `0.6`, Inter 12px
- Y-axis: "Cumulative Cost" — 0 to 100 (arbitrary units, representing relative cost scale)
  - Color: `#475569` opacity `0.6`, Inter 12px
- Axis lines: `#334155` opacity `0.3`, 1px

#### Exponential Curve (Debt)
- Color: `#D9944A` (warm amber), 3px stroke
- Formula: `C(t) = C₀ × (1 + 0.3)^t` (30% compound rate for dramatic visual)
- Data points: `(0, 1), (1, 1.3), (2, 1.7), (3, 2.2), (4, 2.9), (5, 3.7), (6, 4.8), (7, 6.3), (8, 8.2), (9, 10.6), (10, 13.8)` — scaled to fill Y-axis
- Label: "Debt × (1 + Rate)^Time" — Inter, 14px, bold, `#D9944A`, positioned at curve endpoint
- Glow: `4px` soft glow, `#D9944A` opacity `0.15`

#### Flat Line (Regeneration)
- Color: `#4A90D9` (steel blue), 3px stroke, dashed (`8px dash, 4px gap`)
- Data: essentially flat — `(0, 1), (2, 1.1), (4, 1.0), (6, 1.1), (8, 1.0), (10, 1.1)` — slight sawtooth to show "reset each cycle"
- Label: "Regeneration cost (resets each cycle)" — Inter, 13px, `#4A90D9`, positioned at line end

#### CISQ Callout
- Position: anchored near `(8, 8.2)` on the exponential curve
- Box: rounded rectangle, `#1E293B` fill, `#D9944A` border `1px`, padding `12px 16px`
- Text: "$1.52 trillion / year" — Inter, 18px, bold, `#E2E8F0`
- Subtext: "US technical debt — CISQ" — Inter, 11px, `#94A3B8`

### Animation Sequence
1. **Frame 0-60 (0-2s):** The pie chart from shot 5.2 morphs: the amber wedge stretches rightward and upward, reshaping into the exponential curve. The teal wedge collapses and fades. Axes draw in simultaneously.
2. **Frame 60-180 (2-6s):** The exponential curve draws from left to right, starting slow and accelerating. The curve's rising steepness is visually alarming.
3. **Frame 180-270 (6-9s):** The flat teal regeneration line draws in — calm, steady, almost boring by contrast. Its label appears.
4. **Frame 270-360 (9-12s):** The gap between the two lines gets a subtle shaded region (`#D9944A` opacity `0.04`). The CISQ callout fades in near the steep part of the curve.
5. **Frame 360-420 (12-14s):** "Debt × (1 + Rate)^Time" label appears at the curve end. The formula feels mathematical and inevitable.
6. **Frame 420-510 (14-17s):** Hold. The exponential curve continues its gentle upward drift (slight extrapolation animation). The contrast between the two lines is stark.

### Typography
- Curve label: Inter, 14px, bold (600), `#D9944A`
- Flat line label: Inter, 13px, regular (400), `#4A90D9`
- CISQ value: Inter, 18px, bold (700), `#E2E8F0`
- CISQ source: Inter, 11px, regular (400), `#94A3B8`
- Axis labels: Inter, 12px, regular (400), `#475569` opacity `0.6`

### Easing
- Morph transition: `easeInOutCubic` over 60 frames
- Exponential curve draw: `easeIn(quad)` — starts slow, accelerates to match the curve shape
- Flat line draw: `linear` — calm and steady
- CISQ callout fade: `easeOutQuad` over 25 frames
- Shaded region fill: `easeInQuad` over 60 frames

## Narration Sync
> "And those costs compound — literally. Technical debt follows a compound interest curve."
> "CISQ puts the US total at one-point-five-two trillion dollars annually. That's not a metaphor. It's the math of accumulation."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={510}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Morph from pie chart */}
    <Sequence from={0} durationInFrames={60}>
      <MorphTransition
        from="pie_chart_amber_wedge"
        to="exponential_curve_path"
        duration={60} easing="easeInOutCubic" />
    </Sequence>

    {/* Axes */}
    <Sequence from={0}>
      <FadeIn durationInFrames={45}>
        <ChartAxes
          xRange={[0, 10]} yRange={[0, 100]}
          xLabel="Time (years)" yLabel="Cumulative Cost"
          gridColor="#1E293B" gridOpacity={0.08}
          axisColor="#334155" labelColor="#475569" />
      </FadeIn>
    </Sequence>

    {/* Exponential debt curve (amber) */}
    <Sequence from={60}>
      <AnimatedLine
        data={[
          [0, 1], [1, 1.3], [2, 1.7], [3, 2.2], [4, 2.9],
          [5, 3.7], [6, 4.8], [7, 6.3], [8, 8.2], [9, 10.6], [10, 13.8]
        ]}
        color="#D9944A" strokeWidth={3}
        glowRadius={4} glowOpacity={0.15}
        drawDuration={120} easing="easeInQuad" />
    </Sequence>

    {/* Flat regeneration line (teal) */}
    <Sequence from={180}>
      <AnimatedLine
        data={[
          [0, 1], [2, 1.1], [4, 1.0], [6, 1.1], [8, 1.0], [10, 1.1]
        ]}
        color="#4A90D9" strokeWidth={3}
        dashed={{ dash: 8, gap: 4 }}
        drawDuration={90} easing="linear"
        label="Regeneration cost (resets each cycle)"
        labelColor="#4A90D9" />
    </Sequence>

    {/* Shaded gap region */}
    <Sequence from={270}>
      <FillArea
        upperLine="debt_curve" lowerLine="regeneration_line"
        fillColor="#D9944A" opacity={0.04}
        fillDuration={60} easing="easeInQuad" />
    </Sequence>

    {/* CISQ callout */}
    <Sequence from={270}>
      <FadeIn durationInFrames={25}>
        <Callout
          anchorX={8} anchorY={8.2}
          bgColor="#1E293B" borderColor="#D9944A" borderWidth={1}
          padding="12px 16px" borderRadius={8}>
          <Text text="$1.52 trillion / year" font="Inter"
            size={18} weight={700} color="#E2E8F0" />
          <Text text="US technical debt — CISQ" font="Inter"
            size={11} weight={400} color="#94A3B8" />
        </Callout>
      </FadeIn>
    </Sequence>

    {/* Curve label */}
    <Sequence from={360}>
      <FadeIn durationInFrames={20}>
        <Text text="Debt × (1 + Rate)^Time" font="Inter"
          size={14} weight={600} color="#D9944A"
          position="curve-end" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_line_chart",
  "morphFrom": "maintenance_pie_chart",
  "xAxis": { "label": "Time (years)", "range": [0, 10] },
  "yAxis": { "label": "Cumulative Cost", "range": [0, 100] },
  "series": [
    {
      "id": "debt_curve",
      "label": "Debt × (1 + Rate)^Time",
      "color": "#D9944A",
      "formula": "C₀ × (1 + 0.3)^t",
      "data": [[0, 1], [1, 1.3], [2, 1.7], [3, 2.2], [4, 2.9], [5, 3.7], [6, 4.8], [7, 6.3], [8, 8.2], [9, 10.6], [10, 13.8]]
    },
    {
      "id": "regeneration_line",
      "label": "Regeneration cost (resets each cycle)",
      "color": "#4A90D9",
      "style": "dashed",
      "data": [[0, 1], [2, 1.1], [4, 1.0], [6, 1.1], [8, 1.0], [10, 1.1]]
    }
  ],
  "callout": {
    "value": "$1.52 trillion / year",
    "source": "US technical debt — CISQ",
    "anchorPoint": [8, 8.2]
  },
  "narrationSegments": ["part5_compound_returns_003"]
}
```
