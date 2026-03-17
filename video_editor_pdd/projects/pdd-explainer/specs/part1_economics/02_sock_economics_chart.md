[Remotion]

# Section 1.1: Sock Economics Chart — Labor Cost vs Garment Cost

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:34 - 2:52

## Visual Description

An animated price chart showing the historical economics of darning. The Y-axis shows cost relative to an hour of wages. The X-axis spans 1950 to 1975. Two lines animate in: a horizontal "labor cost to darn" line (amber, stays roughly flat) and a declining "new sock cost" line (blue) that starts high in 1950 and drops steadily.

The lines cross around 1960-65. At the crossing point, a glowing label appears: "The Threshold" — the moment when buying new became cheaper than repairing. After the crossing, the gap widens dramatically, making darning visually absurd by the 1970s.

The chart is clean, 3Blue1Brown-style — minimal gridlines, smooth curves, generous whitespace. Numbers appear only where they aid understanding.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Chart area: 280px left margin, 100px right, 140px top, 120px bottom

### Chart/Visual Elements

#### Axes
- X-axis: 1950–1975, major ticks every 5 years, minor ticks every year
- X-axis label: "Year" — Inter, 12px, `#94A3B8` at 0.3
- Y-axis: 0–100% (of hourly wage), major ticks at 25% intervals
- Y-axis label: "Cost (% of hourly wage)" — Inter, 12px, `#94A3B8` at 0.3
- Axis lines: `#334155` at 0.25, 1px
- Grid lines: horizontal only, `#334155` at 0.08, 1px dashed

#### Line 1 — Labor Cost to Darn (Amber)
- Color: `#D9944A`, 3px stroke, slightly rounded caps
- Data: roughly flat line at ~35% of hourly wage (30 min of labor)
- Label: "Cost to darn (time)" — Inter, 12px, `#D9944A` at 0.7, positioned at line end

#### Line 2 — New Sock Cost (Blue)
- Color: `#4A90D9`, 3px stroke
- Data: starts at ~80% in 1950, declines to ~15% by 1975
- Label: "Cost of new socks" — Inter, 12px, `#4A90D9` at 0.7, positioned at line end

#### Crossing Point
- Circle: 8px, `#FFFFFF` at 0.9, with 16px glow `#FFFFFF` at 0.15
- Label: "The Threshold" — Inter, 18px, bold (700), `#E2E8F0` at 0.85, positioned above crossing point
- Annotation line: 1px dashed, `#E2E8F0` at 0.3, connecting label to point

#### Post-Crossing Shading
- Shaded area between the two lines after the crossing: `#4A90D9` at 0.06
- Label: "Darning is irrational" — Inter, 11px, italic, `#94A3B8` at 0.3, centered in shaded area

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in — X-axis left-to-right, Y-axis bottom-to-top. Grid lines fade in.
2. **Frame 30-90 (1-3s):** Both lines draw simultaneously from left to right, reaching 1958. Lines are close together.
3. **Frame 90-150 (3-5s):** Lines continue. The blue "new sock" line drops steeply. Lines converge.
4. **Frame 150-180 (5-6s):** Lines cross at ~1962. Crossing point circle appears with glow. "The Threshold" label fades in above.
5. **Frame 180-300 (6-10s):** Lines continue diverging. Blue line plunges. Gap widens. Shaded area fills between them.
6. **Frame 300-360 (10-12s):** Lines reach 1975. "Darning is irrational" label fades in within the shaded gap.
7. **Frame 360-540 (12-18s):** Hold. Chart complete. Labels fully visible.

### Typography
- Axis labels: Inter, 12px, `#94A3B8` at 0.3
- Tick labels: Inter, 10px, `#94A3B8` at 0.25
- Line labels: Inter, 12px, respective line colors at 0.7
- Crossing label: Inter, 18px, bold (700), `#E2E8F0` at 0.85
- Annotation label: Inter, 11px, italic, `#94A3B8` at 0.3

### Easing
- Axis draw: `easeOut(cubic)` over 30 frames
- Line draw: `linear` (steady reveal, like a chart drawing in real time)
- Crossing point glow: `easeOut(quad)` appear, then `easeInOut(sine)` pulse
- Label fade-ins: `easeOut(quad)` over 15 frames
- Shaded area fill: `easeOut(quad)` over 20 frames

## Narration Sync
> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."
> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

Segments: `part1_economics_002`, `part1_economics_004`

- **2:34** ("In 1950"): Axes appear, lines begin drawing from 1950
- **2:40** ("Darning made sense"): Lines near each other, pre-crossing
- **2:44** ("By the mid-1960s, the math flipped"): Lines cross — "The Threshold" appears
- **2:48** ("Darning became irrational"): Gap widens, shaded area visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Axes */}
    <Sequence from={0} durationInFrames={30}>
      <AnimatedAxes
        xRange={[1950, 1975]} yRange={[0, 100]}
        xLabel="Year" yLabel="Cost (% of hourly wage)"
        gridColor="#334155" gridOpacity={0.08}
      />
    </Sequence>

    {/* Lines draw in */}
    <Sequence from={30}>
      <AnimatedLine
        data={laborCostData} color="#D9944A" strokeWidth={3}
        label="Cost to darn (time)" drawDuration={270}
      />
      <AnimatedLine
        data={sockCostData} color="#4A90D9" strokeWidth={3}
        label="Cost of new socks" drawDuration={270}
      />
    </Sequence>

    {/* Crossing point */}
    <Sequence from={150}>
      <CrossingPoint x={crossX} y={crossY}
        radius={8} glowRadius={16}
        label="The Threshold"
        labelFont="Inter" labelSize={18} labelWeight={700}
        labelColor="#E2E8F0" />
    </Sequence>

    {/* Post-crossing shaded area */}
    <Sequence from={180}>
      <ShadedArea
        upperLine={laborCostData} lowerLine={sockCostData}
        startX={crossX} color="#4A90D9" opacity={0.06}
      />
    </Sequence>

    {/* Annotation */}
    <Sequence from={300}>
      <FadeIn duration={15}>
        <Text text="Darning is irrational" font="Inter" size={11}
          fontStyle="italic" color="#94A3B8" opacity={0.3}
          x={shadedCenterX} y={shadedCenterY} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartType": "dual_line_crossover",
  "xAxis": {
    "label": "Year",
    "range": [1950, 1975],
    "majorInterval": 5,
    "minorInterval": 1
  },
  "yAxis": {
    "label": "Cost (% of hourly wage)",
    "range": [0, 100],
    "majorInterval": 25
  },
  "series": [
    {
      "id": "labor_cost_darn",
      "label": "Cost to darn (time)",
      "color": "#D9944A",
      "data": [
        { "x": 1950, "y": 35 }, { "x": 1955, "y": 34 },
        { "x": 1960, "y": 33 }, { "x": 1965, "y": 33 },
        { "x": 1970, "y": 32 }, { "x": 1975, "y": 32 }
      ]
    },
    {
      "id": "new_sock_cost",
      "label": "Cost of new socks",
      "color": "#4A90D9",
      "data": [
        { "x": 1950, "y": 80 }, { "x": 1955, "y": 55 },
        { "x": 1960, "y": 38 }, { "x": 1962, "y": 33 },
        { "x": 1965, "y": 25 }, { "x": 1970, "y": 18 },
        { "x": 1975, "y": 14 }
      ]
    }
  ],
  "crossingPoint": {
    "x": 1962,
    "y": 33,
    "label": "The Threshold"
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": ["part1_economics_002", "part1_economics_004"]
}
```

---
