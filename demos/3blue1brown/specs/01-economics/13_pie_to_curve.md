# Section 1.12: Pie Chart Morphs to Cost Curve

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 5:45 - 5:58

## Visual Description

The pie chart transforms into an exponentially growing cost curve, showing how maintenance costs don't just dominate - they compound over time. The final visual punch of Part 1.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Smooth transition space

### Morph Transformation

The pie chart elements transform into line chart elements:
- Pie center → Origin point of new chart
- Pie circumference → The curve line
- Amber segment → The rising curve
- Labels → New axis labels

### Target Visualization: Compound Cost Curve

#### Chart Elements
- **X-axis:** Time (Years 1-10)
- **Y-axis:** "Cumulative Maintenance Cost"
- **Curve:** Exponential growth (y = e^(0.3x) scaled)
- **Color:** Amber (#D9944A) - same as maintenance segment

#### Key Features
- Curve starts shallow, becomes steep
- Annotations at key inflection points
- Optional: Ghost line showing "if costs were linear"

### Animation Sequence

1. **Frame 0-90 (0-3s):** Morph begins
   - Pie chart rotates and flattens
   - Circle elongates into horizontal axis
   - Segments flow into curve shape

2. **Frame 90-150 (3-5s):** Axes establish
   - X-axis extends
   - Y-axis grows upward
   - Grid lines fade in

3. **Frame 150-240 (5-8s):** Curve draws
   - Starts at origin
   - Accelerates as it goes right
   - Amber color matches pie segment

4. **Frame 240-300 (8-10s):** Final state
   - Subtle pulse on steep portion
   - Text: "And those costs compound."

### Morph Technical Details

Using SVG path morphing:
- Pie segment arc → Bezier curve
- Maintain color continuity
- Use intermediate key shapes if needed

### Typography

- New title: "Cumulative Maintenance Cost" or just remove title
- Axis labels: Simple year numbers, dollar/cost indicators
- Closing text: "And those costs compound." (bottom, italic, fade in at end)

### Exponential Curve Formula

```javascript
// Normalized exponential for visualization
const curve = (year) => {
  const base = 1.35; // ~35% YoY growth
  return Math.pow(base, year - 1);
};

// Sample points
const data = [
  { year: 1, cost: 1.0 },
  { year: 2, cost: 1.35 },
  { year: 3, cost: 1.82 },
  { year: 4, cost: 2.46 },
  { year: 5, cost: 3.32 },
  { year: 6, cost: 4.48 },
  { year: 7, cost: 6.05 },
  { year: 8, cost: 8.17 },
  { year: 9, cost: 11.03 },
  { year: 10, cost: 14.89 }
];
```

### Easing

- Morph transformation: `easeInOutCubic`
- Curve drawing: `easeOutQuad`
- Text fade: `easeOutCubic`

## Narration Sync

> "And those costs compound."

This single line lands as the curve reaches its steep portion.

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Morph animation */}
  <Sequence from={0} durationInFrames={90}>
    <MorphTransition
      from={<PieChart data={pieData} />}
      to={<LineChartBase />}
      interpolation="morphSVGPath"
    />
  </Sequence>

  {/* Axes establishment */}
  <Sequence from={90} durationInFrames={60}>
    <AnimatedAxes
      xLabel="Years"
      yLabel="Cost"
    />
  </Sequence>

  {/* Curve draw */}
  <Sequence from={150}>
    <ExponentialCurve
      data={compoundCostData}
      color="#D9944A"
      drawDuration={90}
    />
  </Sequence>

  {/* Closing text */}
  <Sequence from={240}>
    <ClosingText text="And those costs compound." />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- The morph should feel smooth and inevitable
- The exponential curve is the "punchline" of Part 1
- Should leave the viewer with a visceral sense of compound cost growth
- 3Blue1Brown signature: mathematical beauty revealing uncomfortable truth

## Color Continuity

Maintain the amber (#D9944A) through the transformation:
- Pie maintenance segment is amber
- Curve line is amber
- Creates visual connection: "this IS that, just over time"

## Optional Enhancement

Add a faint blue "linear" reference line:
- Shows what costs would be if they were constant
- Makes the exponential divergence more dramatic
- Could draw simultaneously with main curve

## Transition

This concludes Part 1. Hard cut or fade to Part 2 (The Paradigm Shift, factory floor).

## End State

The exponential curve should linger briefly as Part 1 ends:
- It's a stark image
- Sets up the problem that Part 2 will offer a solution to
- "How do we escape this curve?" is the implied question
