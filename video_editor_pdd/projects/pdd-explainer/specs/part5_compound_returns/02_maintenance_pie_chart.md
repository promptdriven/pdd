[Remotion]

# Section 5.2: Maintenance Pie Chart — 80-90% of Cost

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:08 - 0:24

## Visual Description

A clean, animated pie chart materializes from center. Two slices: a small teal slice labeled "Initial Development: 10-20%" and a dominant amber/warm slice labeled "Maintenance: 80-90%". The maintenance slice dominates the chart — the visual impact should be immediate and striking.

As the narration mentions McKinsey and Stripe stats, callout annotations appear beside the chart: "40% more on maintenance —McKinsey" and "1/3 of dev time on debt —Stripe". These stats reinforce the pie chart's message.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Pie Chart
- Center: (960, 500)
- Radius: 220px
- Stroke: none (filled slices)
- Drop shadow: 0 4px 20px `#000000` at 0.3

#### Initial Development Slice
- Angle: 54°–72° (15% center value)
- Color: `#4ADE80` (green-teal)
- Label: "Initial Development" — Inter, 14px, semi-bold (600), `#4ADE80`
- Value: "10-20%" — Inter, 20px, bold (700), `#4ADE80`
- Label position: outside slice with connecting line

#### Maintenance Slice
- Angle: 288°–306° (85% center value)
- Color: `#F59E0B` (amber)
- Label: "Maintenance" — Inter, 14px, semi-bold (600), `#F59E0B`
- Value: "80-90%" — Inter, 28px, bold (700), `#F59E0B`
- Label position: outside slice with connecting line
- Slight pull-out: 8px offset from center for emphasis

#### Stat Callouts
- McKinsey: "40% more on maintenance" — Inter, 16px, `#E2E8F0` at 0.8
  - Source: "—McKinsey" — Inter, 12px, `#94A3B8` at 0.5
  - Position: right side, (1340, 380)
  - Left border: 3px `#F59E0B` at 0.6

- Stripe: "⅓ of dev time on debt" — Inter, 16px, `#E2E8F0` at 0.8
  - Source: "—Stripe" — Inter, 12px, `#94A3B8` at 0.5
  - Position: right side, (1340, 480)
  - Left border: 3px `#F59E0B` at 0.6

### Animation Sequence
1. **Frame 0-60 (0-2s):** Pie chart draws in clockwise from 12 o'clock. Maintenance slice first (large), then dev slice. `easeInOutCubic`.
2. **Frame 60-90 (2-3s):** Labels fade in. Maintenance slice pulls out 8px. Values appear.
3. **Frame 90-120 (3-4s):** Hold. The disparity sinks in.
4. **Frame 120-180 (4-6s):** McKinsey callout slides in from right with left-border accent. `easeOutQuad`.
5. **Frame 180-240 (6-8s):** Stripe callout slides in below McKinsey. `easeOutQuad`.
6. **Frame 240-420 (8-14s):** Hold with all elements visible.
7. **Frame 420-480 (14-16s):** Begin fade/morph transition — pie chart starts to compress vertically, hinting at the morphing into the next chart.

### Typography
- Slice labels: Inter, 14px, semi-bold (600)
- Slice values: Inter, 20-28px, bold (700)
- Stat callouts: Inter, 16px, regular (400), `#E2E8F0`
- Stat sources: Inter, 12px, regular (400), `#94A3B8`

### Easing
- Pie draw-in: `easeInOut(cubic)` over 60 frames
- Slice pull-out: `easeOut(back)` over 20 frames
- Label fade: `easeOut(quad)` over 20 frames
- Callout slide: `easeOut(quad)` over 30 frames

## Narration Sync
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it. McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

Segment: `part5_compound_returns_002`

- **0:08** ("Eighty to ninety percent"): Pie chart draws in
- **0:12** ("isn't building"): Labels appear, maintenance slice pulls out
- **0:16** ("McKinsey found"): McKinsey callout slides in
- **0:20** ("Stripe measured"): Stripe callout slides in
- **0:24** (segment ends): Hold, begin morph transition

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Pie chart draw-in */}
    <Sequence from={0}>
      <AnimatedPieChart
        center={[960, 500]} radius={220}
        slices={[
          { label: "Maintenance", value: 85, color: "#F59E0B", pullOut: 8 },
          { label: "Initial Development", value: 15, color: "#4ADE80" }
        ]}
        drawDuration={60}
      />
    </Sequence>

    {/* Labels */}
    <Sequence from={60}>
      <FadeIn duration={20}>
        <PieLabel slice="maintenance" text="80-90%"
          font="Inter" size={28} weight={700} color="#F59E0B" />
        <PieLabel slice="development" text="10-20%"
          font="Inter" size={20} weight={700} color="#4ADE80" />
      </FadeIn>
    </Sequence>

    {/* McKinsey callout */}
    <Sequence from={120}>
      <SlideIn direction="right" duration={30}>
        <StatCallout
          text="40% more on maintenance"
          source="—McKinsey"
          borderColor="#F59E0B"
          x={1340} y={380} />
      </SlideIn>
    </Sequence>

    {/* Stripe callout */}
    <Sequence from={180}>
      <SlideIn direction="right" duration={30}>
        <StatCallout
          text="⅓ of dev time on debt"
          source="—Stripe"
          borderColor="#F59E0B"
          x={1340} y={480} />
      </SlideIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "pie_chart",
  "chartId": "maintenance_cost_pie",
  "slices": [
    { "label": "Maintenance", "range": "80-90%", "color": "#F59E0B", "pullOut": 8 },
    { "label": "Initial Development", "range": "10-20%", "color": "#4ADE80" }
  ],
  "callouts": [
    { "text": "40% more on maintenance", "source": "McKinsey", "color": "#F59E0B" },
    { "text": "⅓ of dev time on debt", "source": "Stripe", "color": "#F59E0B" }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part5_compound_returns_002"]
}
```

---
