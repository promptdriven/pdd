[Remotion]

# Section 5.2: Maintenance Cost — Pie Chart Reveal

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 21:04 - 21:14

## Visual Description
A clean animated donut chart materializes to illustrate the staggering proportion of software cost consumed by maintenance. The chart starts as a single thin ring, then separates into two segments: a small slice labeled "Initial Development: 10-20%" and a dominant slice labeled "Maintenance: 80-90%." The maintenance slice pushes outward with emphasis. Two research callouts animate in below: McKinsey's 40% maintenance overhead finding and Stripe's developer time waste statistic. The visualization grounds the section's argument in concrete economics before transitioning to the compound math.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Pie Chart:** Centered at (960, 420), radius 220px, donut style (inner radius 110px)
  - Maintenance Slice: 85% of circumference (306°), `#D9944A` (warm amber)
  - Initial Dev Slice: 15% of circumference (54°), `#4A90D9` (cool blue)
  - Slice gap: 3px, fill `#0F172A` (background color for clean separation)
  - Inner circle: `#0F172A` with subtle ring `rgba(255,255,255,0.05)` at inner radius
- **Maintenance Label:** "Maintenance: 80–90%" — `#D9944A`, positioned radially outward from slice center, connector line 1px `rgba(255,255,255,0.3)`
- **Dev Label:** "Initial Development: 10–20%" — `#4A90D9`, positioned radially outward from slice center, connector line 1px `rgba(255,255,255,0.3)`
- **Center Stat:** "Software Lifecycle Cost" — `#FFFFFF` at 0.6 opacity, 16px, centered inside donut
- **Research Callout 1 (Y=700):** "Organizations with high tech debt: +40% maintenance cost" — `#FFFFFF` at 0.5 opacity, 16px. Source: "McKinsey, 2024" — `#94A3B8`, 13px
- **Research Callout 2 (Y=750):** "Developers spend ~33% of work week on debt alone" — `#FFFFFF` at 0.5 opacity, 16px. Source: "Stripe, 2018" — `#94A3B8`, 13px

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Thin ring (2px stroke) draws clockwise from 12 o'clock, `rgba(255,255,255,0.2)`. Center text "Software Lifecycle Cost" fades in
2. **Frame 30-90 (1.0-3.0s):** Ring expands to full donut width (110px). Simultaneously, the two slices separate — maintenance slice grows outward 6px with a subtle shadow to emphasize dominance. Colors fill in: amber for maintenance, blue for dev
3. **Frame 90-130 (3.0-4.33s):** Labels animate in — connector lines draw outward, then text fades in at the end of each line. Maintenance label first, then dev label (15-frame stagger)
4. **Frame 130-170 (4.33-5.67s):** Maintenance slice pulses once (scale 1.0→1.04→1.0) with a brief glow `rgba(217,148,74,0.3)` to emphasize the 80-90% figure
5. **Frame 170-220 (5.67-7.33s):** Research callout 1 (McKinsey) slides in from right with 20px horizontal drift, opacity 0→1
6. **Frame 220-270 (7.33-9.0s):** Research callout 2 (Stripe) slides in from right with 20px horizontal drift, opacity 0→1
7. **Frame 270-300 (9.0-10.0s):** Hold at final state

### Typography
- Center Text: Inter, 16px, regular (400), `#FFFFFF` at 0.6 opacity
- Slice Labels: Inter, 20px, semi-bold (600), respective slice colors
- Callout Text: Inter, 16px, regular (400), `#FFFFFF` at 0.5 opacity
- Callout Source: Inter, 13px, regular (400), `#94A3B8`

### Easing
- Ring draw: `easeInOut(cubic)`
- Donut expand: `easeOut(cubic)`
- Slice separation: `easeOut(back(1.2))`
- Label connectors: `easeOut(quad)`
- Label text fade: `easeOut(quad)`
- Maintenance pulse: `easeInOut(sine)`
- Callout slide: `easeOut(cubic)`

## Narration Sync
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it. McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Ring Draw */}
  <Sequence from={0} durationInFrames={30}>
    <DonutRing radius={220} innerRadius={110} strokeColor="rgba(255,255,255,0.2)" />
    <CenterLabel text="Software Lifecycle Cost" />
  </Sequence>

  {/* Pie Segments */}
  <Sequence from={30} durationInFrames={60}>
    <PieSegment
      startAngle={0}
      endAngle={306}
      color="#D9944A"
      radius={226}
      innerRadius={110}
      label="Maintenance: 80–90%"
    />
    <PieSegment
      startAngle={309}
      endAngle={360}
      color="#4A90D9"
      radius={220}
      innerRadius={110}
      label="Initial Development: 10–20%"
    />
  </Sequence>

  {/* Labels */}
  <Sequence from={90} durationInFrames={40}>
    <SliceLabel text="Maintenance: 80–90%" color="#D9944A" />
    <Sequence from={15}>
      <SliceLabel text="Initial Development: 10–20%" color="#4A90D9" />
    </Sequence>
  </Sequence>

  {/* Pulse */}
  <Sequence from={130} durationInFrames={40}>
    <PulseEffect targetSlice="maintenance" scale={1.04} />
  </Sequence>

  {/* Callouts */}
  <Sequence from={170} durationInFrames={50}>
    <ResearchCallout
      text="Organizations with high tech debt: +40% maintenance cost"
      source="McKinsey, 2024"
      y={700}
    />
  </Sequence>
  <Sequence from={220} durationInFrames={50}>
    <ResearchCallout
      text="Developers spend ~33% of work week on debt alone"
      source="Stripe, 2018"
      y={750}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chart": {
    "center": { "x": 960, "y": 420 },
    "radius": 220,
    "innerRadius": 110,
    "sliceGap": 3
  },
  "slices": [
    {
      "label": "Maintenance: 80–90%",
      "percentage": 85,
      "degrees": 306,
      "color": "#D9944A",
      "radiusOffset": 6
    },
    {
      "label": "Initial Development: 10–20%",
      "percentage": 15,
      "degrees": 54,
      "color": "#4A90D9",
      "radiusOffset": 0
    }
  ],
  "callouts": [
    {
      "text": "Organizations with high tech debt: +40% maintenance cost",
      "source": "McKinsey, 2024",
      "y": 700
    },
    {
      "text": "Developers spend ~33% of work week on debt alone",
      "source": "Stripe, 2018",
      "y": 750
    }
  ]
}
```

---
