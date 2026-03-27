[Remotion]

# Section 5.3: Compound Debt Curve — Exponential Growth vs. Flat Regeneration

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:27 - 0:43

## Visual Description

The pie chart morphs into an exponential growth curve. This is the compound interest math made visual:

1. **"Debt × (1 + Rate)^Time" (amber exponential curve, `#D9944A`):** Starts low-left, curves upward exponentially. The formula label appears above the curve as it draws. Each "tick" on the time axis represents a maintenance cycle — and the debt accelerates.

2. **"Regeneration cost" (green flat line, `#5AAA6E`):** A second line appears — flat, low, horizontal. Each regeneration cycle resets debt to zero. Small downward arrows along the green line indicate "debt resets each cycle."

The visual makes the compound interest metaphor visceral. The amber curve reaches terrifying heights while the green line stays calm and level. The CISQ $1.52 trillion figure appears as a label on the amber curve's steep section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal at 150px intervals, `#1E293B` at 0.08

### Chart/Visual Elements

#### Axes
- X-axis: "Time (maintenance cycles)", labeled 0-20, `#94A3B8` at 0.6, Inter 14px
- Y-axis: "Cumulative Cost", `#94A3B8` at 0.6, Inter 14px
- Axis lines: `#334155`, 1.5px

#### Exponential Curve (amber)
- Color: `#D9944A`, 3px solid
- Formula: Debt × (1 + Rate)^Time
- Shape: Starts at y:85%, reaches y:5% by cycle 20 (exponential growth upward)
- Shaded area below: `#D9944A` at 0.08, filling as the curve draws

#### Flat Line (green)
- Color: `#5AAA6E`, 3px solid
- Position: Flat at y:82% — consistently low
- Reset arrows: Small downward arrows (`#5AAA6E` at 0.5) at each cycle tick, indicating debt reset

#### Formula Label
- "Debt × (1 + Rate)^Time" — JetBrains Mono, 18px, `#D9944A` at 0.8, positioned above amber curve at (1100, 200)

#### Flat Line Label
- "Regeneration cost (debt resets each cycle)" — Inter, 16px, `#5AAA6E` at 0.8, positioned near green line at (1100, 700)

#### CISQ Callout
- "$1.52 trillion/year" — Inter, 22px, bold (700), `#E2E8F0`, positioned at the steep part of the amber curve
- "— CISQ" — Inter, 14px, `#94A3B8` at 0.6, below the figure

### Animation Sequence
1. **Frame 0-30 (0-1s):** Morphed axes settle. Grid lines visible. Labels appear.
2. **Frame 30-180 (1-6s):** Amber exponential curve draws left to right. Slow at first, then accelerating upward. Shaded area fills below. Formula label fades in.
3. **Frame 180-270 (6-9s):** Green flat line draws — strikingly level. Reset arrows appear one by one along the line.
4. **Frame 270-330 (9-11s):** Flat line label fades in. The contrast is stark.
5. **Frame 330-390 (11-13s):** CISQ "$1.52 trillion" callout fades in on the amber curve's steep section.
6. **Frame 390-480 (13-16s):** Hold. Both curves fully visible. The exponential gap between them is visceral.

### Typography
- Axis labels: Inter, 14px, regular (400), `#94A3B8` at 0.6
- Formula: JetBrains Mono, 18px, regular (400), `#D9944A` at 0.8
- Flat label: Inter, 16px, regular (400), `#5AAA6E` at 0.8
- CISQ figure: Inter, 22px, bold (700), `#E2E8F0`
- CISQ source: Inter, 14px, regular (400), `#94A3B8` at 0.6

### Easing
- Exponential curve draw: `easeIn(quad)` — accelerating upward
- Green line draw: `easeOut(quad)` — smooth, steady
- Reset arrows: `easeOut(back)` with scale 1.1 → 1.0, staggered 10 frames apart
- Labels: `easeOut(quad)` over 20 frames
- CISQ callout: `easeOut(quad)` over 25 frames

## Narration Sync
> "And those costs compound — literally. Technical debt follows a compound interest curve. CISQ puts the US total at one-point-five-two trillion dollars annually. That's not a metaphor. It's the math of accumulation."

Segment: `part5_compound_returns_002`

- **27.44s** (seg 002): Axes settle — amber curve begins drawing
- **30.00s**: Curve accelerating upward — "Technical debt follows a compound interest curve"
- **34.00s**: Green flat line appears — contrast forms
- **37.00s**: CISQ callout — "one-point-five-two trillion dollars annually"
- **43.20s** (seg 002 ends): Both curves fully visible, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <HorizontalGrid spacing={150} color="#1E293B" opacity={0.08} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        xRange={[0, 20]} xLabel="Time (maintenance cycles)"
        yLabel="Cumulative Cost"
        color="#334155" labelColor="#94A3B8"
      />
    </Sequence>

    {/* Exponential debt curve */}
    <Sequence from={30}>
      <AnimatedLine
        data={debtExponentialData}
        color="#D9944A" strokeWidth={3}
        drawDuration={150} easing="easeInQuad"
      />
      <ShadedArea
        upperBound={debtExponentialData}
        lowerBound={baseline}
        color="#D9944A" opacity={0.08}
        fillDuration={150}
      />
    </Sequence>

    {/* Formula label */}
    <Sequence from={90}>
      <FadeIn duration={20}>
        <Text text="Debt × (1 + Rate)^Time"
          font="JetBrains Mono" size={18}
          color="#D9944A" opacity={0.8}
          x={1100} y={200} />
      </FadeIn>
    </Sequence>

    {/* Green flat regeneration line */}
    <Sequence from={180}>
      <AnimatedLine
        data={regenerationFlatData}
        color="#5AAA6E" strokeWidth={3}
        drawDuration={90} easing="easeOutQuad"
      />
    </Sequence>

    {/* Reset arrows */}
    <Sequence from={210}>
      <StaggeredArrows
        positions={cycleTicks}
        color="#5AAA6E" opacity={0.5}
        stagger={10} easing="easeOutBack"
      />
    </Sequence>

    {/* Flat line label */}
    <Sequence from={270}>
      <FadeIn duration={20}>
        <Text text="Regeneration cost (debt resets each cycle)"
          font="Inter" size={16}
          color="#5AAA6E" opacity={0.8}
          x={1100} y={700} />
      </FadeIn>
    </Sequence>

    {/* CISQ callout */}
    <Sequence from={330}>
      <FadeIn duration={25}>
        <Text text="$1.52 trillion/year" font="Inter" size={22}
          weight={700} color="#E2E8F0" x={750} y={180} />
        <Text text="— CISQ" font="Inter" size={14}
          color="#94A3B8" opacity={0.6} x={750} y={210} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "dual_curve_chart",
  "chartId": "compound_debt_vs_regeneration",
  "xAxis": { "label": "Time (maintenance cycles)", "range": [0, 20] },
  "yAxis": { "label": "Cumulative Cost" },
  "series": [
    {
      "id": "debt_exponential",
      "label": "Debt × (1 + Rate)^Time",
      "color": "#D9944A",
      "type": "exponential",
      "data": [
        { "x": 0, "y": 0.05 }, { "x": 2, "y": 0.07 },
        { "x": 4, "y": 0.10 }, { "x": 6, "y": 0.14 },
        { "x": 8, "y": 0.20 }, { "x": 10, "y": 0.30 },
        { "x": 12, "y": 0.42 }, { "x": 14, "y": 0.58 },
        { "x": 16, "y": 0.72 }, { "x": 18, "y": 0.85 },
        { "x": 20, "y": 0.95 }
      ]
    },
    {
      "id": "regeneration_flat",
      "label": "Regeneration cost (debt resets each cycle)",
      "color": "#5AAA6E",
      "type": "flat",
      "data": [
        { "x": 0, "y": 0.08 }, { "x": 20, "y": 0.08 }
      ]
    }
  ],
  "annotations": [
    { "type": "callout", "text": "$1.52 trillion/year", "source": "CISQ", "position": "steep_section" }
  ],
  "narrationSegments": ["part5_compound_returns_002"]
}
```

---
