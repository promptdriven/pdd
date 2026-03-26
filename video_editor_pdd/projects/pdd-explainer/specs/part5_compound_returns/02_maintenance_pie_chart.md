[Remotion]

# Section 5.2: Maintenance Pie Chart — Where Software Cost Really Goes

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:08 - 0:24

## Visual Description
A bold pie chart materializes on screen showing the overwhelming proportion of software cost spent on maintenance versus initial development. The chart starts empty and fills in two dramatic sweeps:

1. A small teal wedge sweeps in — "Initial Development: 10-20%" — almost modest.
2. An enormous amber wedge sweeps to fill the remaining 80-90% — "Maintenance: 80-90%" — visually dominating the frame.

Below the chart, two data citations fade in: "McKinsey: +40% maintenance overhead from tech debt" and "Stripe: 33% of dev time spent on debt." These reinforce the staggering scale. The overall feeling is: the thing you think is the hard part (building) is the small part. The real cost is keeping it alive.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines

### Chart/Visual Elements

#### Pie Chart
- Center: `(960, 460)` (slightly above center to leave room for citations)
- Outer radius: `280px`
- Inner radius: `0` (solid pie, not donut)
- Rotation start: `-90°` (12 o'clock position)

#### Wedge 1 — Initial Development
- Angle: `54°` (15% of 360°, midpoint of 10-20% range)
- Color: `#4A90D9` (steel blue)
- Label: "Initial Development" — Inter, 16px, bold, `#4A90D9`
- Value: "10-20%" — Inter, 28px, bold, `#E2E8F0`
- Label position: leader line from wedge center to upper-left

#### Wedge 2 — Maintenance
- Angle: `306°` (85% of 360°, midpoint of 80-90% range)
- Color: `#D9944A` (warm amber)
- Label: "Maintenance" — Inter, 16px, bold, `#D9944A`
- Value: "80-90%" — Inter, 36px, bold, `#E2E8F0`
- Label position: leader line from wedge center to right side

#### Data Citations
- Citation 1: "McKinsey: +40% maintenance overhead" — Inter, 13px, `#94A3B8`, positioned at `(960, 780)`
- Citation 2: "Stripe: 33% of dev week on debt" — Inter, 13px, `#94A3B8`, positioned at `(960, 810)`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Chart outline fades in — a thin `1px` circle at `#334155` opacity `0.3`.
2. **Frame 30-90 (1-3s):** Teal wedge sweeps clockwise from 12 o'clock, covering 54°. Label and "10-20%" appear at end of sweep.
3. **Frame 90-210 (3-7s):** Amber wedge sweeps clockwise to fill the remaining 306°. The visual weight is overwhelming. "80-90%" label appears in large text. "Maintenance" label fades in.
4. **Frame 210-270 (7-9s):** Slight scale pulse on the amber wedge (`1.0→1.03→1.0`) to emphasize dominance.
5. **Frame 270-360 (9-12s):** McKinsey and Stripe citations fade in sequentially, 30 frames apart.
6. **Frame 360-480 (12-16s):** Hold. The chart sits, letting the proportion sink in.

### Typography
- Percentage labels: Inter, 28-36px, bold (700), `#E2E8F0`
- Category labels: Inter, 16px, bold (600), respective wedge colors
- Citations: Inter, 13px, regular (400), `#94A3B8`

### Easing
- Wedge sweep: `easeInOutCubic`
- Label fade-in: `easeOutQuad` over 20 frames
- Amber pulse: `easeInOutSine` over 30 frames
- Citation fade: `easeOutQuad` over 25 frames

## Narration Sync
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it."
> "McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Chart outline */}
    <Sequence from={0}>
      <FadeIn durationInFrames={30}>
        <Circle cx={960} cy={460} r={280}
          stroke="#334155" strokeWidth={1} fill="none" opacity={0.3} />
      </FadeIn>
    </Sequence>

    {/* Initial Development wedge (teal) */}
    <Sequence from={30}>
      <AnimatedWedge
        cx={960} cy={460} r={280}
        startAngle={-90} sweepAngle={54}
        color="#4A90D9"
        sweepDuration={60} easing="easeInOutCubic" />
      <Sequence from={60}>
        <FadeIn durationInFrames={20}>
          <PieLabel text="Initial Development" value="10-20%"
            labelColor="#4A90D9" valueColor="#E2E8F0"
            valueSize={28} position="upper-left" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Maintenance wedge (amber) */}
    <Sequence from={90}>
      <AnimatedWedge
        cx={960} cy={460} r={280}
        startAngle={-36} sweepAngle={306}
        color="#D9944A"
        sweepDuration={120} easing="easeInOutCubic" />
      <Sequence from={120}>
        <FadeIn durationInFrames={20}>
          <PieLabel text="Maintenance" value="80-90%"
            labelColor="#D9944A" valueColor="#E2E8F0"
            valueSize={36} position="right" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Amber pulse */}
    <Sequence from={210}>
      <ScalePulse target="maintenance_wedge"
        fromScale={1.0} toScale={1.03}
        durationInFrames={30} easing="easeInOutSine" />
    </Sequence>

    {/* Citations */}
    <Sequence from={270}>
      <FadeIn durationInFrames={25}>
        <Text text="McKinsey: +40% maintenance overhead"
          font="Inter" size={13} color="#94A3B8"
          x={960} y={780} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={300}>
      <FadeIn durationInFrames={25}>
        <Text text="Stripe: 33% of dev week on debt"
          font="Inter" size={13} color="#94A3B8"
          x={960} y={810} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_pie_chart",
  "center": [960, 460],
  "radius": 280,
  "wedges": [
    {
      "id": "initial_development",
      "label": "Initial Development",
      "value": "10-20%",
      "midpointPct": 15,
      "color": "#4A90D9",
      "sweepAngle": 54
    },
    {
      "id": "maintenance",
      "label": "Maintenance",
      "value": "80-90%",
      "midpointPct": 85,
      "color": "#D9944A",
      "sweepAngle": 306
    }
  ],
  "citations": [
    "McKinsey: +40% maintenance overhead from tech debt",
    "Stripe: 33% of dev week on debt"
  ],
  "narrationSegments": ["part5_compound_returns_002"]
}
```
