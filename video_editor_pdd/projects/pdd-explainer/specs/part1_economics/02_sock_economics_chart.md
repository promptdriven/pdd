[Remotion]

# Section 1.2: Sock Economics — Labor vs. Garment Cost

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 2:33 - 2:45

## Visual Description
An animated line chart showing the economics of sock darning from 1950 to 2020. Two lines — "Labor Cost (per hour)" and "Garment Cost (pair of socks)" — start with garment cost high relative to labor, then cross around 1960-65 at "The Threshold." After crossing, the lines diverge dramatically: labor rises while garment cost plummets. The crossing point is highlighted with a glowing circle and label. The chart uses warm, vintage-inspired colors on the project's dark background to evoke the 1950s-60s era.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.06)`, 5 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1400px wide x 600px tall, centered (left margin 260px, top margin 200px)
- **X-Axis:** Years 1950–2020, labeled every decade, white `#FFFFFF` at 0.5 opacity
- **Y-Axis:** "Relative Cost" (unitless index 0–100), labeled at 0, 25, 50, 75, 100, white `#FFFFFF` at 0.5 opacity
- **Labor Cost Line:** `#D9944A` (warm amber), 3px stroke, starts at 30 (1950), rises steadily to 85 (2020)
- **Garment Cost Line:** `#4A90D9` (cool blue), 3px stroke, starts at 70 (1950), drops to 5 (2020)
- **Crossing Point:** Glowing circle at ~1962, value ~45, radius 8px, fill `#FFFFFF` at 0.8 opacity, glow `rgba(255,255,255,0.3)` blur 12px
- **Crossing Label:** "The Threshold" — white, positioned above crossing point at Y offset -40px
- **Legend:** Top-right corner — two color swatches with labels

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Axes draw in — X-axis sweeps left-to-right, Y-axis sweeps bottom-to-top. Axis labels fade in (opacity 0→0.5)
2. **Frame 30-120 (1.0-4.0s):** Both lines draw simultaneously from 1950 rightward. Labor line rises; garment line falls. They approach each other
3. **Frame 120-150 (4.0-5.0s):** Lines cross at ~1962. Crossing point circle pulses in (scale 0→1.2→1.0). "The Threshold" label fades in above
4. **Frame 150-270 (5.0-9.0s):** Lines continue diverging dramatically post-crossing. Garment cost plummets; labor cost climbs. The gap widens
5. **Frame 270-310 (9.0-10.33s):** Shaded area between the two lines fills in with a semi-transparent gradient (`rgba(217,148,74,0.1)` to `rgba(74,144,217,0.1)`) to emphasize the divergence
6. **Frame 310-360 (10.33-12.0s):** Hold at final state. Legend fades in at top-right

### Typography
- Chart Title: Inter, 32px, semi-bold (600), `#FFFFFF`, opacity 0.9, top-center of chart
- Axis Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.5
- "The Threshold" Label: Inter, 22px, semi-bold (600), `#FFFFFF`, opacity 0.9
- Legend Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.7

### Easing
- Axis draw: `easeOut(cubic)`
- Line draw: `linear` (constant speed along X-axis for time-accurate feel)
- Crossing pulse: `easeOut(back(1.5))`
- Label fades: `easeOut(quad)`
- Area fill: `easeIn(quad)`

## Narration Sync
> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."
> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Axes */}
  <Sequence from={0} durationInFrames={30}>
    <AnimatedAxis
      xRange={[1950, 2020]}
      yRange={[0, 100]}
      xLabel="Year"
      yLabel="Relative Cost"
    />
  </Sequence>

  {/* Lines */}
  <Sequence from={30} durationInFrames={240}>
    <AnimatedLine
      data={laborCostData}
      color="#D9944A"
      strokeWidth={3}
    />
    <AnimatedLine
      data={garmentCostData}
      color="#4A90D9"
      strokeWidth={3}
    />
  </Sequence>

  {/* Crossing Point */}
  <Sequence from={120} durationInFrames={30}>
    <CrossingHighlight
      x={1962}
      y={45}
      label="The Threshold"
    />
  </Sequence>

  {/* Divergence Area */}
  <Sequence from={270} durationInFrames={40}>
    <AreaFill upperLine={laborCostData} lowerLine={garmentCostData} />
  </Sequence>

  {/* Legend */}
  <Sequence from={310}>
    <ChartLegend items={[
      { label: "Labor Cost (per hour)", color: "#D9944A" },
      { label: "Garment Cost (pair of socks)", color: "#4A90D9" }
    ]} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "xAxis": { "label": "Year", "range": [1950, 2020], "tickInterval": 10 },
  "yAxis": { "label": "Relative Cost", "range": [0, 100] },
  "laborCost": [
    { "year": 1950, "value": 30 },
    { "year": 1955, "value": 35 },
    { "year": 1960, "value": 42 },
    { "year": 1965, "value": 50 },
    { "year": 1970, "value": 55 },
    { "year": 1980, "value": 65 },
    { "year": 1990, "value": 72 },
    { "year": 2000, "value": 78 },
    { "year": 2010, "value": 82 },
    { "year": 2020, "value": 85 }
  ],
  "garmentCost": [
    { "year": 1950, "value": 70 },
    { "year": 1955, "value": 60 },
    { "year": 1960, "value": 48 },
    { "year": 1965, "value": 38 },
    { "year": 1970, "value": 28 },
    { "year": 1980, "value": 18 },
    { "year": 1990, "value": 12 },
    { "year": 2000, "value": 8 },
    { "year": 2010, "value": 6 },
    { "year": 2020, "value": 5 }
  ],
  "crossingPoint": { "year": 1962, "value": 45 },
  "backgroundColor": "#0F172A"
}
```

---
