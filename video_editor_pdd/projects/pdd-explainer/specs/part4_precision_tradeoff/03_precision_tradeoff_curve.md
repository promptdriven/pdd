[Remotion]

# Section 4.3: Precision Tradeoff Curve — Tests vs. Required Prompt Detail

**Tool:** Remotion
**Duration:** ~23s (690 frames @ 30fps)
**Timestamp:** 0:24 - 0:48

## Visual Description

An animated graph showing the inverse relationship between test count and required prompt precision. This is the core analytical visual of Part 4.

**Axes:** X-axis labeled "Number of Tests" (0 to 50+). Y-axis labeled "Required Prompt Precision" (low to high). Both axes drawn in the 3B1B clean-graph style.

**The Curve:** An inverse/hyperbolic curve draws from upper-left (few tests, high precision needed) to lower-right (many tests, low precision needed). The curve is smooth and deliberate — not a straight line but a dramatic drop-off that flattens.

**Animated Annotation:** A glowing dot traverses the curve. At the left extreme (2–3 tests), a callout appears: "50-line prompt. Every edge case specified." At the right extreme (40+ tests), a second callout: "10-line prompt. Tests handle constraints." The dot moves along the curve, showing the transition.

**Zone Shading:** The area under the curve is lightly shaded — left zone in amber (high-effort prompting) fading to blue on the right (low-effort prompting, tests do the work).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal and vertical at 160px intervals, `#1E293B` at 0.06

### Chart/Visual Elements

#### Axes
- X-axis: 0 to 50+, labeled at 0, 10, 20, 30, 40, 50, `#94A3B8` at 0.6, Inter 14px
- Y-axis: "Low" at bottom, "High" at top, `#94A3B8` at 0.6, Inter 14px
- X-axis label: "Number of Tests" — Inter 16px, semi-bold (600), `#94A3B8`
- Y-axis label: "Required Prompt Precision" — Inter 16px, semi-bold (600), `#94A3B8`, rotated -90°
- Axis lines: `#334155`, 1.5px
- Chart area: x: 200–1720, y: 120–880

#### Inverse Curve
- Color: `#E2E8F0`, 3px stroke
- Shape: f(x) = k / (x + c) mapped to chart coordinates — steep initial drop, long tail
- Data points: (0, 0.95), (5, 0.70), (10, 0.45), (15, 0.32), (20, 0.25), (30, 0.18), (40, 0.14), (50, 0.12)

#### Zone Shading
- Under curve, left half: `#D9944A` at 0.06 (amber — high prompt effort zone)
- Under curve, right half: `#4A90D9` at 0.06 (blue — test-driven zone)
- Gradient transition at x = 20

#### Traversing Dot
- `#FFFFFF`, 10px circle, `#FFFFFF` glow at 0.2, 16px radius
- Moves along curve from left to right

#### Callouts
- Left callout (at x ≈ 3): "50-line prompt\nEvery edge case specified" — Inter 14px, `#D9944A`, with connecting line to curve
- Right callout (at x ≈ 45): "10-line prompt\nTests handle constraints" — Inter 14px, `#4A90D9`, with connecting line to curve

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Axes draw in from origin. Grid lines fade in. Axis labels appear.
2. **Frame 45-180 (1.5-6s):** Inverse curve draws from left to right. Starts steep (dramatic drop), then flattens. Zone shading fills beneath as the line progresses.
3. **Frame 180-240 (6-8s):** Glowing dot appears at the left extreme of the curve. Left callout animates in: "50-line prompt / Every edge case specified."
4. **Frame 240-450 (8-15s):** Dot traverses the curve from left to right. Zone shading transitions from amber to blue beneath. The dot accelerates slightly as the curve flattens.
5. **Frame 450-540 (15-18s):** Dot arrives at the right extreme. Right callout animates in: "10-line prompt / Tests handle constraints."
6. **Frame 540-690 (18-23s):** Hold. Both callouts visible. The curve and its meaning are clear. Slow fade-out.

### Typography
- Axis labels: Inter, 14px, regular (400), `#94A3B8` at 0.6
- Axis titles: Inter, 16px, semi-bold (600), `#94A3B8`
- Callout text: Inter, 14px, regular (400), respective accent colors
- Callout connecting lines: respective colors at 0.3, 1px

### Easing
- Axes draw: `easeOut(quad)` over 30 frames
- Curve draw: `easeInOut(cubic)` over 135 frames
- Zone shading fill: `easeOut(quad)`, tracking curve progress
- Dot traversal: `easeInOut(cubic)` over 210 frames
- Callout appear: `easeOut(back)` with scale 0.95→1.0 over 20 frames
- Fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "This maps directly to PDD."
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segments: `part4_precision_tradeoff_002`

- **24.74s** (seg 002): Graph axes begin drawing — "This maps directly to PDD"
- **28.00s**: Curve begins drawing
- **33.00s**: Dot at left extreme — "prompt needs to specify everything"
- **38.00s**: Dot traversing curve — "Edge cases. Error handling."
- **43.00s**: Dot at right extreme — "Tests handle the constraints"
- **48.18s** (seg 002 ends): Hold, begin fade

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={690}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <GridLines spacing={160} color="#1E293B" opacity={0.06} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        xRange={[0, 50]} xLabel="Number of Tests"
        yRange={[0, 1]} yLabel="Required Prompt Precision"
        yTickLabels={["Low", "High"]}
        color="#334155" labelColor="#94A3B8"
        chartArea={{ x: 200, y: 120, width: 1520, height: 760 }}
        drawDuration={45}
      />
    </Sequence>

    {/* Zone shading */}
    <Sequence from={45}>
      <ZoneShading
        curve={precisionCurveData}
        leftColor="#D9944A" rightColor="#4A90D9"
        opacity={0.06} transitionX={20}
        fillDuration={135}
      />
    </Sequence>

    {/* Inverse curve */}
    <Sequence from={45}>
      <AnimatedLine
        data={precisionCurveData}
        color="#E2E8F0" strokeWidth={3}
        drawDuration={135} easing="easeInOutCubic"
      />
    </Sequence>

    {/* Traversing dot + callouts */}
    <Sequence from={180}>
      <TraversingDot
        path={precisionCurveData}
        dotColor="#FFFFFF" dotSize={10}
        glowColor="#FFFFFF" glowOpacity={0.2}
        traverseDuration={270}
        startDelay={0} /* appears at left */
      />
    </Sequence>

    {/* Left callout */}
    <Sequence from={180}>
      <Callout
        text={"50-line prompt\nEvery edge case specified"}
        position={calloutLeftPos}
        color="#D9944A" lineColor="#D9944A"
        font="Inter" size={14}
      />
    </Sequence>

    {/* Right callout */}
    <Sequence from={450}>
      <Callout
        text={"10-line prompt\nTests handle constraints"}
        position={calloutRightPos}
        color="#4A90D9" lineColor="#4A90D9"
        font="Inter" size={14}
      />
    </Sequence>

    {/* Fade out */}
    <Sequence from={630}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "line_chart",
  "chartId": "precision_tradeoff_curve",
  "xAxis": { "label": "Number of Tests", "range": [0, 50], "tickInterval": 10 },
  "yAxis": { "label": "Required Prompt Precision", "range": [0, 1], "tickLabels": ["Low", "High"] },
  "series": [
    {
      "id": "precision_curve",
      "label": "Required Prompt Precision",
      "color": "#E2E8F0",
      "data": [
        { "x": 0, "y": 0.95 }, { "x": 5, "y": 0.70 },
        { "x": 10, "y": 0.45 }, { "x": 15, "y": 0.32 },
        { "x": 20, "y": 0.25 }, { "x": 30, "y": 0.18 },
        { "x": 40, "y": 0.14 }, { "x": 50, "y": 0.12 }
      ]
    }
  ],
  "annotations": [
    { "type": "callout", "x": 3, "text": "50-line prompt\nEvery edge case specified", "color": "#D9944A" },
    { "type": "callout", "x": 45, "text": "10-line prompt\nTests handle constraints", "color": "#4A90D9" }
  ],
  "zones": [
    { "range": [0, 20], "color": "#D9944A", "label": "High prompt effort" },
    { "range": [20, 50], "color": "#4A90D9", "label": "Test-driven precision" }
  ],
  "narrationSegments": ["part4_precision_tradeoff_002"]
}
```

---
