[Remotion]

# Section 1.2: Sock Price Chart — Labor vs Garment Cost Over Time

**Tool:** Remotion
**Duration:** ~30s (900 frames @ 30fps)
**Timestamp:** 0:04 - 0:34

## Visual Description

An animated line chart showing the economics of sock darning from 1950 to 2020. The X-axis spans decades; the Y-axis represents cost relative to an hour of wages. Two lines: a warm amber "Labor cost of darning" line that stays relatively flat, and a cool blue "Cost of new socks" line that starts high and falls steadily.

The lines cross around 1960-65 — this is "The Threshold" moment. Before the crossing, darning is rational. After, buying new socks is cheaper. By 2020, the blue line is essentially at zero relative to labor cost. The crossing point gets a pulsing highlight label.

The chart uses a clean 3Blue1Brown-inspired aesthetic — dark background, thin precise lines, mathematical elegance.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: `#1E293B` at 0.06, 80px horizontal spacing, 60px vertical spacing

### Chart/Visual Elements

#### Axes
- X-axis: 1950-2020, major ticks every 10 years, minor every 5
- X-axis label: "Year" — Inter, 11px, `#64748B` at 0.5
- Y-axis: relative cost (0-100%), no explicit numbers — implied by position
- Y-axis label: "Cost (Relative to Hourly Wage)" — Inter, 11px, `#64748B` at 0.5, rotated -90°
- Axis lines: `#334155` at 0.4, 1.5px
- Tick labels: JetBrains Mono, 10px, `#94A3B8` at 0.5

#### Line 1 — Labor Cost of Darning (amber)
- Color: `#D9944A`, 2.5px stroke
- Path: relatively flat line from (1950, 45%) to (2020, 50%) — slight upward drift
- Glow: 6px Gaussian blur, `#D9944A` at 0.12
- Label: "Labor cost (darning)" — Inter, 11px, `#D9944A` at 0.7, positioned at line endpoint

#### Line 2 — Cost of New Socks (blue)
- Color: `#4A90D9`, 2.5px stroke
- Path: starts at (1950, 80%), falls steeply through 1960s, flattens near zero by 2000
- Glow: 6px Gaussian blur, `#4A90D9` at 0.12
- Label: "Cost of new socks" — Inter, 11px, `#4A90D9` at 0.7, positioned at line endpoint

#### Crossing Point — "The Threshold"
- Position: approximately (1962, 47%)
- Circle: 8px, `#E2E8F0` at 0.8, with 16px glow at 0.2
- Label: "The Threshold" — Inter, 16px, bold (700), `#E2E8F0` at 0.9
- Connecting line: 1px dashed, `#E2E8F0` at 0.3, from circle to label
- Pulse: circle breathes between 0.6 and 1.0 opacity on 40-frame cycle

#### Divergence Shading (post-threshold)
- Shaded area between lines after 1965: `#4A90D9` at 0.04
- Grows wider as lines diverge — visual emphasis on the economic gap

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in — X-axis left-to-right, Y-axis bottom-to-top. Grid lines fade in.
2. **Frame 30-60 (1-2s):** Tick labels appear. Y-axis label fades in. Chart title area ready.
3. **Frame 60-180 (2-6s):** Amber line draws from 1950 rightward, keeping pace with narration about 1950 economics. Blue line draws simultaneously but faster — it starts high and begins to descend.
4. **Frame 180-240 (6-8s):** Lines approach crossing point. Circle appears at threshold. "The Threshold" label fades in with connecting dashed line.
5. **Frame 240-300 (8-10s):** Crossing point pulses. Brief hold — the 3B1B "notice this" moment.
6. **Frame 300-600 (10-20s):** Lines continue past threshold. Blue line plunges. Shaded divergence area fills progressively. By 2020, the gap is enormous.
7. **Frame 600-750 (20-25s):** Divergence area fully shaded. Line labels appear at endpoints.
8. **Frame 750-900 (25-30s):** Hold on complete chart. Crossing point continues pulsing.

### Typography
- Chart title area: Inter, 12px, semi-bold (600), `#94A3B8` at 0.4, letter-spacing 3px
- Axis labels: Inter, 11px, `#64748B` at 0.5
- Tick labels: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Threshold label: Inter, 16px, bold (700), `#E2E8F0` at 0.9
- Line labels: Inter, 11px, respective line colors at 0.7

### Easing
- Axis draw: `easeOut(cubic)` over 30 frames
- Line draw: `easeInOut(quad)` continuous over respective durations
- Threshold circle appear: `easeOut(back)` over 15 frames
- Label fade-in: `easeOut(quad)` over 20 frames
- Shading fill: `easeOut(quad)` progressive
- Threshold pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "This isn't nostalgia. It's economics."
> "In 1950, a wool sock cost real money relative to an hour of labor. Darning made sense. You'd spend thirty minutes to save a dollar."
> "By the mid-1960s, the math flipped. A new sock cost less than the time to repair the old one. Darning became irrational."

Segments: `part1_economics_005`, `part1_economics_006`, `part1_economics_007`

- **0:04** ("isn't nostalgia. It's economics"): Chart axes begin drawing
- **0:08** ("In 1950, a wool sock"): Lines begin drawing from 1950
- **0:19** ("By the mid-1960s"): Crossing point approaches, threshold label appears
- **0:27** ("Darning became irrational"): Lines fully diverged, chart complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={900}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <ChartGrid hSpacing={80} vSpacing={60} color="#1E293B" opacity={0.06} />

    {/* Axes */}
    <Sequence from={0}>
      <AnimatedAxis axis="x" from={1950} to={2020}
        majorTick={10} minorTick={5}
        color="#334155" opacity={0.4} width={1.5}
        labelFont="JetBrains Mono" labelSize={10}
        labelColor="#94A3B8" labelOpacity={0.5}
        drawDuration={30} />
      <AnimatedAxis axis="y" label="Cost (Relative to Hourly Wage)"
        color="#334155" opacity={0.4} width={1.5}
        labelFont="Inter" labelSize={11}
        labelColor="#64748B" labelOpacity={0.5}
        drawDuration={30} />
    </Sequence>

    {/* Amber line — labor cost */}
    <Sequence from={60}>
      <AnimatedLine data={laborCostData} color="#D9944A"
        width={2.5} glow={{ blur: 6, opacity: 0.12 }}
        drawDuration={540} />
    </Sequence>

    {/* Blue line — sock cost */}
    <Sequence from={60}>
      <AnimatedLine data={sockCostData} color="#4A90D9"
        width={2.5} glow={{ blur: 6, opacity: 0.12 }}
        drawDuration={540} />
    </Sequence>

    {/* Divergence shading */}
    <Sequence from={300}>
      <AreaBetween upper={laborCostData} lower={sockCostData}
        color="#4A90D9" opacity={0.04}
        startX={1965} fillDuration={300} />
    </Sequence>

    {/* Threshold crossing */}
    <Sequence from={180}>
      <ThresholdMarker cx={thresholdX} cy={thresholdY}
        radius={8} color="#E2E8F0" opacity={0.8}
        glowRadius={16} glowOpacity={0.2}
        pulse={{ min: 0.6, max: 1.0, period: 40 }}
        label="The Threshold" labelFont="Inter"
        labelSize={16} labelWeight={700}
        dashedLine />
    </Sequence>

    {/* Line labels at endpoints */}
    <Sequence from={600}>
      <FadeIn duration={20}>
        <LineLabel text="Labor cost (darning)" color="#D9944A"
          opacity={0.7} position="end" />
        <LineLabel text="Cost of new socks" color="#4A90D9"
          opacity={0.7} position="end" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "sock_economics",
  "chartType": "dual_line",
  "xAxis": { "label": "Year", "range": [1950, 2020], "majorTick": 10 },
  "yAxis": { "label": "Cost (Relative to Hourly Wage)", "range": [0, 100] },
  "series": [
    {
      "id": "labor_cost",
      "label": "Labor cost (darning)",
      "color": "#D9944A",
      "dataPoints": [
        { "x": 1950, "y": 45 }, { "x": 1960, "y": 47 },
        { "x": 1970, "y": 48 }, { "x": 1980, "y": 48 },
        { "x": 1990, "y": 49 }, { "x": 2000, "y": 49 },
        { "x": 2010, "y": 50 }, { "x": 2020, "y": 50 }
      ]
    },
    {
      "id": "sock_cost",
      "label": "Cost of new socks",
      "color": "#4A90D9",
      "dataPoints": [
        { "x": 1950, "y": 80 }, { "x": 1955, "y": 65 },
        { "x": 1960, "y": 52 }, { "x": 1965, "y": 40 },
        { "x": 1970, "y": 28 }, { "x": 1980, "y": 15 },
        { "x": 1990, "y": 8 }, { "x": 2000, "y": 4 },
        { "x": 2010, "y": 2 }, { "x": 2020, "y": 1 }
      ]
    }
  ],
  "threshold": { "x": 1962, "y": 47, "label": "The Threshold" },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_005", "part1_economics_006", "part1_economics_007"]
}
```

---
