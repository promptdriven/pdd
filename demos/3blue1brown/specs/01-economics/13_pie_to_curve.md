# Section 1.12: Pie Chart Morphs to Cost Curve

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 5:45 - 5:58

## Visual Description

The pie chart morphs into an exponentially growing cost curve labeled "Technical debt follows compound interest: Debt x (1 + Rate)^Time". A second, flat line appears labeled "Regeneration cost (debt resets each cycle)". The contrast between compound growth and flat reset is the final visual punch of Part 1.

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
- **Curve 1 (Technical Debt):** Exponential growth (y = e^(0.3x) scaled)
  - Color: Amber (#D9944A) - same as maintenance segment
  - Label: "Technical debt follows compound interest: Debt x (1 + Rate)^Time"
- **Line 2 (Regeneration Cost):** Flat horizontal line near the bottom
  - Color: Cool blue (#4A90D9) - same as generation color
  - Label: "Regeneration cost (debt resets each cycle)"
  - This line stays flat because regeneration resets the debt to zero each cycle

#### Key Features
- Exponential curve starts shallow, becomes steep
- Flat regeneration line provides stark visual contrast
- The growing gap between the two lines IS the argument for PDD

### Animation Sequence

1. **Frame 0-90 (0-3s):** Morph begins
   - Pie chart rotates and flattens
   - Circle elongates into horizontal axis
   - Segments flow into curve shape

2. **Frame 90-150 (3-5s):** Axes establish
   - X-axis extends
   - Y-axis grows upward
   - Grid lines fade in

3. **Frame 150-210 (5-7s):** Exponential curve draws
   - Starts at origin
   - Accelerates as it goes right
   - Amber color matches pie segment
   - Label appears: "Technical debt follows compound interest: Debt x (1 + Rate)^Time"

4. **Frame 210-260 (7-8.5s):** Regeneration line appears
   - Flat blue line draws across near the bottom
   - Label: "Regeneration cost (debt resets each cycle)"
   - The contrast with the exponential curve is stark

5. **Frame 260-300 (8.5-10s):** Final state
   - Subtle pulse on steep portion of exponential curve
   - The gap between the two lines widens visually

### Morph Technical Details

Using SVG path morphing:
- Pie segment arc → Bezier curve
- Maintain color continuity
- Use intermediate key shapes if needed

### Typography

- Curve label: "Technical debt follows compound interest: Debt x (1 + Rate)^Time" (near the exponential curve)
- Regeneration label: "Regeneration cost (debt resets each cycle)" (near the flat line)
- Axis labels: Simple year numbers, cost indicators

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

> "And those costs compound—literally. Technical debt follows a compound interest curve. Unless you regenerate. Then the debt resets."

The exponential curve draws as "compound" is said. The flat regeneration line appears as "regenerate" is said.

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

  {/* Exponential debt curve */}
  <Sequence from={150}>
    <ExponentialCurve
      data={compoundCostData}
      color="#D9944A"
      drawDuration={60}
      label="Technical debt follows compound interest: Debt × (1 + Rate)^Time"
    />
  </Sequence>

  {/* Flat regeneration line */}
  <Sequence from={210}>
    <FlatLine
      y={regenerationCost}
      color="#4A90D9"
      drawDuration={50}
      label="Regeneration cost (debt resets each cycle)"
    />
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

## Key Visual Contrast

The flat blue regeneration line vs. the exponential amber debt curve is the visual thesis of Part 1:
- Patching: costs compound over time (exponential growth)
- Regeneration: costs reset each cycle (flat line)
- The divergence between these two lines IS the economic argument for PDD

## Transition

This concludes Part 1. Hard cut or fade to Part 2 (The Paradigm Shift, factory floor).

## End State

The exponential curve should linger briefly as Part 1 ends:
- It's a stark image
- Sets up the problem that Part 2 will offer a solution to
- "How do we escape this curve?" is the implied question
