[Remotion]

# Section 5.2: Maintenance Pie Chart — 80-90% of Software Cost

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:00 - 0:16

## Visual Description

A clean, animated pie chart materializes from the center of the screen. Two segments fill in:

1. **"Maintenance: 80-90%" (amber, `#D9944A`):** The dominant segment — fills nearly the entire circle. The number "80-90%" animates counting up.
2. **"Initial Development: 10-20%" (blue, `#4A90D9`):** A thin sliver. The contrast is stark and intentional.

The pie chart uses the 3B1B aesthetic: clean, dark background, smooth segment fills, minimal but precise labeling. The labels sit outside the chart with thin connector lines. The visual is meant to shock — most viewers assume building is the expensive part.

This visual overlaps with the title card — it begins materializing behind the title text mid-segment-001, becoming the primary visual as the title fades out.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines — clean focus on the chart

### Chart/Visual Elements

#### Pie Chart
- Center: (960, 540) — dead center
- Radius: 220px
- Stroke: `#1E293B`, 2px outline on segments
- Rotation: starts at 12 o'clock (top), draws clockwise

#### Segments
- Maintenance (amber): `#D9944A`, 80-90% of circle (~288-324°)
- Initial Development (blue): `#4A90D9`, 10-20% of circle (~36-72°)

#### Labels
- "Maintenance: 80-90%" — Inter, 20px, semi-bold (600), `#D9944A`, positioned right of chart at (1250, 440)
- "Initial Development: 10-20%" — Inter, 20px, semi-bold (600), `#4A90D9`, positioned right of chart at (1250, 520)
- Connector lines: 1px, respective colors at 0.4, from segment midpoint to label

#### Statistic Callouts (appear below chart)
- "McKinsey: 40% more on maintenance with high tech debt" — Inter, 14px, `#94A3B8` at 0.6
- "Stripe: 1/3 of dev week lost to debt" — Inter, 14px, `#94A3B8` at 0.6

### Animation Sequence
1. **Frame 0-30 (0-1s):** Pie chart outline circle draws from top, clockwise. Thin stroke only.
2. **Frame 30-120 (1-4s):** Maintenance segment fills clockwise with a smooth wipe. Orange glow as it fills. Number counts up: "0%" → "80-90%".
3. **Frame 120-150 (4-5s):** Development segment fills the remaining sliver. Blue accent. "10-20%" appears.
4. **Frame 150-180 (5-6s):** Labels animate in with connector lines.
5. **Frame 180-300 (6-10s):** Hold. Chart fully visible. Statistic callouts fade in one at a time below chart.
6. **Frame 300-420 (10-14s):** Chart continues to hold. Maintenance segment pulses subtly.
7. **Frame 420-480 (14-16s):** Pie chart begins morphing — segments flatten into the base of an exponential curve for the next visual.

### Typography
- Segment labels: Inter, 20px, semi-bold (600), respective colors
- Percentage counters: Inter, 28px, bold (700), respective colors
- Statistic callouts: Inter, 14px, regular (400), `#94A3B8` at 0.6

### Easing
- Pie fill: `easeInOut(cubic)` — smooth radial wipe
- Number count: `easeOut(quad)` — quick start, gentle landing
- Label fade-in: `easeOut(quad)` over 20 frames
- Callout fade-in: `easeOut(quad)` over 15 frames, staggered 20 frames apart
- Morph to curve: `easeInOut(cubic)` over 60 frames

## Narration Sync
> "Now, let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it. McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

Segment: `part5_compound_returns_001`

- **0.00s** (seg 001): Pie chart outline begins drawing — "Now, let's zoom out"
- **6.00s**: Maintenance segment filling — "Eighty to ninety percent..."
- **15.00s**: Stats visible — "Stripe measured developers..."
- **27.08s** (seg 001 ends): Pie chart begins morphing to curve

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Pie chart outline */}
    <Sequence from={0}>
      <StrokeDraw duration={30}>
        <Circle cx={960} cy={540} r={220}
          stroke="#1E293B" strokeWidth={2} fill="none" />
      </StrokeDraw>
    </Sequence>

    {/* Maintenance segment fill */}
    <Sequence from={30}>
      <PieSegment
        cx={960} cy={540} r={220}
        startAngle={0} endAngle={306}
        color="#D9944A"
        fillDuration={90} easing="easeInOutCubic"
      />
      <AnimatedCounter
        from={0} to={85} suffix="%"
        label="80-90%"
        font="Inter" size={28} weight={700}
        color="#D9944A"
        duration={90} x={960} y={540}
      />
    </Sequence>

    {/* Development segment fill */}
    <Sequence from={120}>
      <PieSegment
        cx={960} cy={540} r={220}
        startAngle={306} endAngle={360}
        color="#4A90D9"
        fillDuration={30}
      />
    </Sequence>

    {/* Labels */}
    <Sequence from={150}>
      <FadeIn duration={20}>
        <PieLabel text="Maintenance: 80-90%" color="#D9944A"
          position={[1250, 440]} connectorFrom={[1180, 440]} />
        <PieLabel text="Initial Development: 10-20%" color="#4A90D9"
          position={[1250, 520]} connectorFrom={[1180, 480]} />
      </FadeIn>
    </Sequence>

    {/* Statistic callouts */}
    <Sequence from={200}>
      <FadeIn duration={15}>
        <Text text="McKinsey: 40% more on maintenance with high tech debt"
          color="#94A3B8" opacity={0.6} size={14} x={960} y={720} />
      </FadeIn>
    </Sequence>
    <Sequence from={220}>
      <FadeIn duration={15}>
        <Text text="Stripe: 1/3 of dev week lost to debt"
          color="#94A3B8" opacity={0.6} size={14} x={960} y={750} />
      </FadeIn>
    </Sequence>

    {/* Morph transition to curve */}
    <Sequence from={420}>
      <PieToExponentialMorph duration={60} easing="easeInOutCubic" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "pie_chart",
  "chartId": "maintenance_cost_split",
  "segments": [
    {
      "id": "maintenance",
      "label": "Maintenance",
      "percentage": "80-90%",
      "color": "#D9944A",
      "degrees": 306
    },
    {
      "id": "initial_development",
      "label": "Initial Development",
      "percentage": "10-20%",
      "color": "#4A90D9",
      "degrees": 54
    }
  ],
  "statistics": [
    { "source": "McKinsey", "finding": "40% more on maintenance with high technical debt" },
    { "source": "Stripe", "finding": "1/3 of developer work week lost to debt" },
    { "source": "CISQ", "finding": "$1.52 trillion annually in US" }
  ],
  "narrationSegments": ["part5_compound_returns_001"]
}
```

---
