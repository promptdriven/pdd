# Section 1.11: Maintenance Pie Chart

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 4:40 - 4:55

## Visual Description

A clean pie chart materializes showing the true cost distribution of software: 10-20% initial development, 80-90% maintenance. A stark visualization of where money actually goes.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Chart centered

### Chart Elements

#### Pie Chart
- **Segment 1: Initial Development**
  - Size: 15% (middle of 10-20% range)
  - Color: Cool blue (#4A90D9)
  - Label: "Initial Development"
  - Percentage: "10-20%"

- **Segment 2: Maintenance**
  - Size: 85%
  - Color: Warm amber (#D9944A)
  - Label: "Maintenance"
  - Percentage: "80-90%"

#### Visual Styling
- 3D effect: Subtle, not cheesy
- Drop shadow: Soft
- Segment separation: Slight gap (2-3px)
- Stroke: White, 1px

### Animation Sequence

1. **Frame 0-60 (0-2s):** Chaos from previous section fades out
2. **Frame 60-120 (2-4s):** Pie chart base appears (circle outline)
3. **Frame 120-180 (4-6s):** Blue segment draws in (clock-wise, small)
   - "Initial Development" label appears
4. **Frame 180-300 (6-10s):** Amber segment draws in (clock-wise, huge)
   - The visual impact of how much bigger it is
   - "Maintenance" label appears
5. **Frame 300-360 (10-12s):** Percentages fade in
6. **Frame 360-450 (12-15s):** Hold with subtle pulse on maintenance segment

### Segment Draw Animation

The segments should "grow" like a pie being sliced:
- Start from 12 o'clock position
- Blue segment: 0° → ~55° (small arc)
- Amber segment: ~55° → 360° (enormous arc)

The disparity in arc length tells the story visually.

### Typography

- Chart title: "Where Software Costs Go" (top, 32pt, white)
- Labels: Sans-serif, 18pt, white
- Percentages: Bold, 24pt, segment colors

### Easing

- Segment draw: `easeInOutCubic`
- Labels fade: `easeOutQuad`
- Pulse: `sin` wave on scale (1.0 → 1.02 → 1.0)

## Narration Sync

> "It's maintaining it. Patching it. Navigating around all the previous patches."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Title */}
  <Sequence from={60}>
    <ChartTitle text="Where Software Costs Go" />
  </Sequence>

  {/* Pie chart */}
  <Sequence from={120}>
    <AnimatedPieChart>
      <PieSegment
        value={15}
        color="#4A90D9"
        label="Initial Development"
        percentage="10-20%"
        drawStart={0}
        drawDuration={60}
      />
      <PieSegment
        value={85}
        color="#D9944A"
        label="Maintenance"
        percentage="80-90%"
        drawStart={60}
        drawDuration={120}
      />
    </AnimatedPieChart>
  </Sequence>

  {/* Percentages */}
  <Sequence from={300}>
    <PercentageLabels />
  </Sequence>

  {/* Pulse effect */}
  <Sequence from={360}>
    <PulseEffect segment="maintenance" />
  </Sequence>
</Sequence>
```

## Data Source Note

The 80-90% maintenance figure is well-documented in software engineering literature:
- Robert Glass, "Frequently Forgotten Fundamental Facts about Software Engineering"
- Various industry studies on total cost of ownership

## Visual Style Notes

- Clean, minimal, data-forward
- The chart should feel like a revelation
- The amber segment's size should be visually striking
- No unnecessary decoration - let the data speak

## Alternative Visualization (Fallback)

If pie chart feels too basic, consider:
- Stacked bar chart (horizontal)
- Waffle chart (10x10 grid of squares)
- Treemap with nested rectangles

## Transition

The pie chart morphs into an exponential cost curve (Section 1.12).
