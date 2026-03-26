[Remotion]

# Section 1.2: Sock Price Chart — Labor vs Garment Cost Over Time

**Tool:** Remotion
**Duration:** ~21s (630 frames @ 30fps)
**Timestamp:** 0:23 - 0:44

## Visual Description

An animated line chart showing the economics of socks from 1950 to 2020. The Y-axis represents cost in labor-hours, the X-axis is time. Two lines tell the story:

1. **Blue line ("Labor cost"):** The rising value of an hour of human work. Starts low in 1950, climbs steadily.
2. **Amber line ("Garment cost"):** The cost of quality wool socks. Starts high in 1950 (roughly equal to an hour's wages), drops over time as manufacturing scales.

The lines cross around 1960-65 — "The Threshold" — where it became cheaper to buy new socks than to darn old ones. After the crossing, the lines diverge dramatically. By 2020, socks are essentially free relative to labor.

The crossing point gets a special highlight treatment: a glowing dot, a label "The Threshold", and a brief pulse animation to draw the eye.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal dashed at `#1E293B` at 0.1, every 20% of Y-axis

### Chart/Visual Elements

#### Axes
- X-axis: 1950 to 2020, tick marks every decade, labels at bottom
  - Color: `#475569` at 0.6, Inter 12px
- Y-axis: "Cost (Labor Hours)" — 0 to 4 hours
  - Color: `#475569` at 0.6, Inter 12px
- Axis lines: `#334155` at 0.3, 1px

#### Lines
- **Labor cost (blue):** `#4A90D9`, 3px stroke, starts ~1.0 at 1950, rises to ~3.5 at 2020
  - Data: smooth bezier through (1950, 1.0), (1960, 1.3), (1970, 1.8), (1980, 2.2), (1990, 2.6), (2000, 3.0), (2020, 3.5)
  - Label: "Hour of labor" — Inter, 13px, `#4A90D9`, positioned at line end
- **Garment cost (amber):** `#D9944A`, 3px stroke, starts ~1.0 at 1950, drops to ~0.1 at 2020
  - Data: smooth bezier through (1950, 1.0), (1960, 0.7), (1965, 0.5), (1970, 0.35), (1980, 0.2), (2000, 0.12), (2020, 0.08)
  - Label: "Pair of wool socks" — Inter, 13px, `#D9944A`, positioned at line end

#### Crossing Point
- Position: approximately 1962, ~0.85 labor-hours
- Glowing dot: 8px, `#FFFFFF` at 0.9, glow radius 20px, `#FFFFFF` at 0.15
- Label: "The Threshold" — Inter, 16px, bold, `#E2E8F0`, offset above crossing point

#### Divergence Area
- Shaded region between the two lines after the crossing: gradient from `#4A90D9` at 0.05 at top to `#D9944A` at 0.05 at bottom

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in. Grid lines appear.
2. **Frame 30-90 (1-3s):** Both lines begin drawing simultaneously from 1950. The lines are close together, nearly overlapping.
3. **Frame 90-180 (3-6s):** Lines reach 1960s. They converge and CROSS. Crossing point glows. "The Threshold" label appears.
4. **Frame 180-360 (6-12s):** Lines diverge dramatically. The blue rises, amber drops. Shaded divergence area fills in gradually.
5. **Frame 360-480 (12-16s):** Lines reach 2020. The gap is enormous. Final labels appear at line ends.
6. **Frame 480-630 (16-21s):** Hold. Crossing point pulses gently. The visual settles.

### Typography
- Chart title: Inter, 20px, bold (700), `#E2E8F0`, top-left
- Axis labels: Inter, 12px, `#475569` at 0.6
- Line labels: Inter, 13px, respective line colors
- "The Threshold": Inter, 16px, bold (700), `#E2E8F0`

### Easing
- Line draw: `easeInOut(cubic)` over duration
- Crossing glow: `easeOut(quad)` bloom over 15 frames
- Label appear: `easeOut(quad)` over 20 frames
- Divergence fill: `easeIn(quad)` as area grows
- Crossing pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "In 1950, a wool sock cost about an hour of wages to buy. Darning — repairing it — made economic sense. You'd spend fifteen minutes fixing what cost an hour to replace."
> "Or K. By the mid 1960s, manufacturing scaled. Prices dropped. Now look at the chart. The lines cross."

Segments: `part1_economics_006`, `part1_economics_007`

- **23.94s** ("In 1950, a wool sock"): Chart axes appear, lines begin drawing
- **29s** ("Darning — repairing it"): Lines approaching crossing point
- **34.62s** ("By the mid 1960s"): Lines crossing, "The Threshold" appears
- **40s** ("The lines cross"): Divergence visible, dramatic gap widening

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={630}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Axes and grid */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <ChartAxes
          xRange={[1950, 2020]} yRange={[0, 4]}
          xLabel="Year" yLabel="Cost (Labor Hours)"
          gridColor="#1E293B" gridOpacity={0.1}
          axisColor="#334155" labelColor="#475569" />
      </FadeIn>
    </Sequence>

    {/* Labor cost line (blue) */}
    <Sequence from={30}>
      <AnimatedLine
        data={[
          [1950, 1.0], [1960, 1.3], [1970, 1.8],
          [1980, 2.2], [1990, 2.6], [2000, 3.0], [2020, 3.5]
        ]}
        color="#4A90D9" strokeWidth={3}
        drawDuration={420} easing="easeInOutCubic"
        label="Hour of labor" labelColor="#4A90D9" />
    </Sequence>

    {/* Garment cost line (amber) */}
    <Sequence from={30}>
      <AnimatedLine
        data={[
          [1950, 1.0], [1960, 0.7], [1965, 0.5],
          [1970, 0.35], [1980, 0.2], [2000, 0.12], [2020, 0.08]
        ]}
        color="#D9944A" strokeWidth={3}
        drawDuration={420} easing="easeInOutCubic"
        label="Pair of wool socks" labelColor="#D9944A" />
    </Sequence>

    {/* Divergence shaded area */}
    <Sequence from={180}>
      <FillArea
        upperLine="labor_cost" lowerLine="garment_cost"
        startX={1962} fillColor="#4A90D9" opacity={0.05}
        fillDuration={180} />
    </Sequence>

    {/* Crossing point highlight */}
    <Sequence from={90}>
      <GlowDot x={1962} y={0.85} radius={8}
        color="#FFFFFF" glowRadius={20} glowOpacity={0.15}
        fadeIn={15} pulse={60} />
      <FadeIn duration={20}>
        <Text text="The Threshold" font="Inter" size={16}
          weight={700} color="#E2E8F0"
          x={1962} yOffset={-30} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_line_chart",
  "xAxis": { "label": "Year", "range": [1950, 2020], "ticks": "decade" },
  "yAxis": { "label": "Cost (Labor Hours)", "range": [0, 4] },
  "series": [
    {
      "id": "labor_cost",
      "label": "Hour of labor",
      "color": "#4A90D9",
      "data": [[1950, 1.0], [1960, 1.3], [1970, 1.8], [1980, 2.2], [1990, 2.6], [2000, 3.0], [2020, 3.5]]
    },
    {
      "id": "garment_cost",
      "label": "Pair of wool socks",
      "color": "#D9944A",
      "data": [[1950, 1.0], [1960, 0.7], [1965, 0.5], [1970, 0.35], [1980, 0.2], [2000, 0.12], [2020, 0.08]]
    }
  ],
  "crossingPoint": { "x": 1962, "y": 0.85, "label": "The Threshold" },
  "narrationSegments": ["part1_economics_006", "part1_economics_007"]
}
```

---
