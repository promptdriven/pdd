[Remotion]

# Section 1.2: Sock Economics Chart — The Threshold

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:34 - 2:52

## Visual Description

An animated price chart shows the economics of sock darning. The X-axis spans from 1950 to 2020. Two lines draw themselves across time: a rising amber line labeled "Labor cost (per hour)" and a falling blue line labeled "Sock cost." The lines cross around 1960-65 — this crossing point highlights with a glow and the label "The Threshold" appears.

Before the crossing, the area between the lines is shaded light green (darning makes sense — sock costs more than labor). After the crossing, the area shades light red (darning is irrational — labor costs more than a new sock). The divergence accelerates dramatically by 2020, with socks essentially free relative to labor.

The chart style is clean, 3Blue1Brown-inspired — dark background, smooth curves, mathematical precision. The data is real: wool socks cost roughly an hour's wages in 1950; by 2020, a multi-pack costs minutes of minimum wage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: horizontal at $10 intervals, `#1E293B` at 0.08; vertical at decade markers, `#1E293B` at 0.08

### Chart/Visual Elements

#### Axes
- X-axis: 1950 to 2020, positioned at y: 800, `#475569` at 0.5, 2px
- Y-axis: $0 to $30 (adjusted for relative labor), positioned at x: 200, `#475569` at 0.5, 2px
- Axis labels: Inter, 12px, `#64748B` at 0.5
- Decade markers on X: "1950", "1960", "1970", "1980", "1990", "2000", "2010", "2020"

#### Line 1 — Labor Cost (rising)
- Color: `#D9944A` (warm amber), 3px stroke
- Path: starts at ~$2/hr (1950), rises steadily to ~$25/hr (2020)
- Smooth bezier curve
- Label: "Labor cost (per hour)" — Inter, 13px, `#D9944A` at 0.7, positioned at line endpoint

#### Line 2 — Sock Cost (falling)
- Color: `#4A90D9` (cool blue), 3px stroke
- Path: starts at ~$8 (1950, relative to era), falls to ~$1 (2020)
- Smooth bezier curve
- Label: "Sock cost" — Inter, 13px, `#4A90D9` at 0.7, positioned at line endpoint

#### Crossing Point
- Position: approximately x: 1962 on chart, where lines intersect
- Highlight: 12px radius circle, `#E2E8F0` at 0.8, 2px stroke
- Glow: 20px Gaussian blur, `#E2E8F0` at 0.15
- Label: "The Threshold" — Inter, 16px, semi-bold (600), `#E2E8F0`, positioned above crossing with thin leader line

#### Shaded Areas
- Pre-crossing (1950-1962): between the two lines, `#5AAA6E` at 0.06 (green — darning rational)
- Post-crossing (1962-2020): between the two lines, `#EF4444` at 0.04 (red — darning irrational)
- Areas have feathered edges at the crossing point

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in. Grid lines appear. Decade markers fade in.
2. **Frame 30-120 (1-4s):** Both lines draw simultaneously from left to right. The labor line rises, the sock line falls. They approach the crossing point.
3. **Frame 120-150 (4-5s):** Lines cross. The crossing point circle and glow appear. "The Threshold" label fades in with a slight bounce.
4. **Frame 150-240 (5-8s):** Lines continue drawing to 2020. The divergence becomes dramatic. Shaded areas fill in — green pre-crossing, red post-crossing.
5. **Frame 240-360 (8-12s):** Hold on chart. Labels appear at line endpoints.
6. **Frame 360-420 (12-14s):** Camera zooms into the post-2000 region. The gap is enormous. A small annotation appears: "$25/hr labor vs. $0.50 sock."
7. **Frame 420-540 (14-18s):** Hold. The irrationality of darning is visually self-evident.

### Typography
- Axis labels: Inter, 12px, `#64748B` at 0.5
- Line labels: Inter, 13px, respective colors at 0.7
- "The Threshold": Inter, 16px, semi-bold (600), `#E2E8F0`
- Annotation: Inter, 12px, `#CBD5E1` at 0.6

### Easing
- Line draw: `easeInOut(cubic)` over draw duration
- Crossing highlight: `easeOut(back(1.5))` scale bounce, 15 frames
- "The Threshold" label: `easeOut(cubic)` with 5px bounce
- Shaded area fill: `easeOut(quad)` over 30 frames
- Camera zoom: `easeInOut(cubic)` over 60 frames

## Narration Sync
> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."
> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

Segment: `part1_002`

- **2:34** ("In 1950, a wool sock cost real money"): Lines begin drawing, early portion of chart visible
- **2:40** ("Darning made sense"): Pre-crossing green area visible
- **2:44** ("By the mid-1960s, the math flipped"): Lines cross, threshold highlights
- **2:48** ("Darning became irrational"): Post-crossing red area fills, divergence visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Chart grid and axes */}
    <Sequence from={0}>
      <ChartAxes
        xRange={[1950, 2020]} yRange={[0, 30]}
        xPos={200} yPos={800}
        gridColor="#1E293B" gridOpacity={0.08}
        axisColor="#475569" axisWidth={2}
        xLabels={['1950','1960','1970','1980','1990','2000','2010','2020']}
        drawDuration={30}
      />
    </Sequence>

    {/* Both lines draw simultaneously */}
    <Sequence from={30}>
      <AnimatedLine
        data={laborCostData} color="#D9944A" width={3}
        drawDuration={210}
        label="Labor cost (per hour)" labelSize={13}
      />
      <AnimatedLine
        data={sockCostData} color="#4A90D9" width={3}
        drawDuration={210}
        label="Sock cost" labelSize={13}
      />
    </Sequence>

    {/* Shaded areas */}
    <Sequence from={150}>
      <ShadedArea
        between={[laborCostData, sockCostData]}
        range={[1950, 1962]} color="#5AAA6E" opacity={0.06}
        fadeDuration={30}
      />
      <ShadedArea
        between={[laborCostData, sockCostData]}
        range={[1962, 2020]} color="#EF4444" opacity={0.04}
        fadeDuration={30}
      />
    </Sequence>

    {/* Crossing point highlight */}
    <Sequence from={120}>
      <CrossingHighlight
        position={crossingPoint} radius={12}
        color="#E2E8F0" glowRadius={20} glowOpacity={0.15}
        label="The Threshold" labelSize={16}
      />
    </Sequence>

    {/* Zoom into modern gap */}
    <Sequence from={360}>
      <CameraZoom
        target={{ x: 1800, y: 400 }} scale={1.8}
        duration={60}
      />
      <Annotation
        text="$25/hr labor vs. $0.50 sock"
        position={[1600, 500]} color="#CBD5E1" opacity={0.6}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "sock_economics",
  "xAxis": { "label": "Year", "range": [1950, 2020], "unit": "year" },
  "yAxis": { "label": "Cost (relative)", "range": [0, 30], "unit": "USD" },
  "series": [
    {
      "name": "Labor cost (per hour)",
      "color": "#D9944A",
      "dataPoints": [
        { "x": 1950, "y": 2 },
        { "x": 1960, "y": 4 },
        { "x": 1970, "y": 7 },
        { "x": 1980, "y": 12 },
        { "x": 1990, "y": 15 },
        { "x": 2000, "y": 18 },
        { "x": 2010, "y": 22 },
        { "x": 2020, "y": 25 }
      ]
    },
    {
      "name": "Sock cost",
      "color": "#4A90D9",
      "dataPoints": [
        { "x": 1950, "y": 8 },
        { "x": 1960, "y": 5 },
        { "x": 1970, "y": 3 },
        { "x": 1980, "y": 2 },
        { "x": 1990, "y": 1.5 },
        { "x": 2000, "y": 1 },
        { "x": 2010, "y": 0.75 },
        { "x": 2020, "y": 0.5 }
      ]
    }
  ],
  "crossingPoint": { "x": 1962, "label": "The Threshold" },
  "shadedAreas": [
    { "range": [1950, 1962], "color": "#5AAA6E", "meaning": "Darning rational" },
    { "range": [1962, 2020], "color": "#EF4444", "meaning": "Darning irrational" }
  ],
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part1_002"]
}
```

---
