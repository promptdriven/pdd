[Remotion]

# Section 1.2: Sock Price vs. Labor Cost Chart

**Tool:** Remotion
**Duration:** ~24s (720 frames @ 30fps)
**Timestamp:** 0:24 - 0:48

## Visual Description

An animated line chart showing the economic threshold that killed darning. Two lines plotted from 1950 to 2020:

1. **"Labor cost" (amber):** Starts low, rises steadily — the hourly cost of a person's time.
2. **"Garment cost" (blue):** Starts high (relative to wages), drops over time as manufacturing gets cheaper.

The lines cross around 1960-65. At the crossing point, a label "The Threshold" appears with a glowing highlight. After the crossing, the lines diverge dramatically — by 2020, socks are essentially free relative to labor.

The chart uses the 3B1B aesthetic: dark background, clean axes, smooth line draws, minimal labels. The crossing point is the emotional beat — the moment darning became irrational.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal at 200px intervals, `#1E293B` at 0.08

### Chart/Visual Elements

#### Axes
- X-axis: 1950 to 2020, labeled at decades, `#94A3B8` at 0.6, Inter 14px
- Y-axis: "Cost (relative to hourly wage)", `#94A3B8` at 0.6, Inter 14px
- Axis lines: `#334155`, 1.5px

#### Lines
- Labor cost (amber): `#D9944A`, 3px, starts at y:80% → rises to y:15% by 2020
- Garment cost (blue): `#4A90D9`, 3px, starts at y:20% → drops to y:90% by 2020
- Crossing point: ~1962, highlighted with radial glow `#FFFFFF` at 0.15, 20px radius

#### Annotations
- "The Threshold" label: Inter 18px, bold, `#E2E8F0`, appears at crossing point with connecting line
- "Darning makes sense" — small label left of crossing, `#5AAA6E` at 0.6
- "Darning is irrational" — small label right of crossing, `#EF4444` at 0.6

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in. Grid lines fade in. Y-axis label appears.
2. **Frame 30-90 (1-3s):** Both lines begin drawing simultaneously from 1950, left to right. Slow, deliberate.
3. **Frame 90-150 (3-5s):** Lines approach the crossing point. Pace slows slightly to build tension.
4. **Frame 150-180 (5-6s):** Lines cross. Flash at intersection. "The Threshold" label animates in with a subtle scale-up.
5. **Frame 180-360 (6-12s):** Lines continue diverging post-crossing. The gap between them widens dramatically. "Darning is irrational" label fades in.
6. **Frame 360-600 (12-20s):** Lines reach 2020. Hold. The divergence is stark — garment line near bottom, labor line near top.
7. **Frame 600-720 (20-24s):** Chart begins morphing — axes relabel for the code chart transition. Amber line fades, blue line holds.

### Typography
- Axis labels: Inter, 14px, regular (400), `#94A3B8` at 0.6
- "The Threshold": Inter, 18px, bold (700), `#E2E8F0`
- Zone labels: Inter, 13px, regular (400), respective colors at 0.6

### Easing
- Line draw: `easeInOut(cubic)` — steady with subtle deceleration near crossing
- Threshold label: `easeOut(back)` with scale 1.05 → 1.0
- Zone labels: `easeOut(quad)` over 20 frames
- Divergence: `easeIn(quad)` — accelerating separation

## Narration Sync
> "This isn't nostalgia. It's economics."
> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."
> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

Segments: `part1_economics_004`, `part1_economics_005`

- **23.54s** (seg 004): Chart axes begin drawing — "This isn't nostalgia. It's economics."
- **25.0s**: Lines begin drawing from 1950
- **30.0s**: Lines approach crossing — "Darning made sense"
- **37.88s** (seg 004 ends): Post-crossing, divergence visible
- **38.12s** (seg 005): "By the mid-1960s, the math flipped" — divergence accelerates
- **47.10s** (seg 005 ends): Chart fully drawn, holding at 2020

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={720}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Grid */}
    <HorizontalGrid spacing={200} color="#1E293B" opacity={0.08} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        xRange={[1950, 2020]} xLabel="Year"
        yLabel="Cost (relative to hourly wage)"
        color="#334155" labelColor="#94A3B8"
      />
    </Sequence>

    {/* Lines drawing */}
    <Sequence from={30}>
      <AnimatedLine
        data={laborCostData}
        color="#D9944A" strokeWidth={3}
        drawDuration={570} easing="easeInOutCubic"
      />
      <AnimatedLine
        data={garmentCostData}
        color="#4A90D9" strokeWidth={3}
        drawDuration={570} easing="easeInOutCubic"
      />
    </Sequence>

    {/* Crossing point highlight */}
    <Sequence from={150}>
      <CrossingHighlight
        position={crossingPoint}
        glowColor="#FFFFFF" glowOpacity={0.15}
        label="The Threshold"
        labelFont="Inter" labelSize={18}
      />
    </Sequence>

    {/* Zone labels */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <Text text="Darning is irrational" color="#EF4444"
          opacity={0.6} size={13} />
      </FadeIn>
    </Sequence>

    {/* Morph transition */}
    <Sequence from={600}>
      <ChartMorph target="code_cost_chart" duration={120} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "line_chart",
  "chartId": "sock_price_vs_labor",
  "xAxis": { "label": "Year", "range": [1950, 2020], "tickInterval": 10 },
  "yAxis": { "label": "Cost (relative to hourly wage)", "range": [0, 1] },
  "series": [
    {
      "id": "labor_cost",
      "label": "Labor cost",
      "color": "#D9944A",
      "data": [
        { "x": 1950, "y": 0.2 }, { "x": 1960, "y": 0.35 },
        { "x": 1970, "y": 0.5 }, { "x": 1980, "y": 0.6 },
        { "x": 1990, "y": 0.7 }, { "x": 2000, "y": 0.78 },
        { "x": 2010, "y": 0.82 }, { "x": 2020, "y": 0.85 }
      ]
    },
    {
      "id": "garment_cost",
      "label": "Garment cost (relative)",
      "color": "#4A90D9",
      "data": [
        { "x": 1950, "y": 0.8 }, { "x": 1960, "y": 0.5 },
        { "x": 1965, "y": 0.35 }, { "x": 1970, "y": 0.25 },
        { "x": 1980, "y": 0.18 }, { "x": 1990, "y": 0.12 },
        { "x": 2000, "y": 0.1 }, { "x": 2020, "y": 0.08 }
      ]
    }
  ],
  "annotations": [
    { "type": "crossing_point", "x": 1962, "label": "The Threshold" }
  ],
  "narrationSegments": ["part1_economics_004", "part1_economics_005"]
}
```

---
