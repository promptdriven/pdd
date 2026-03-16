[Remotion]

# Section 5.3: Compound Debt Curve — Exponential Growth Visualization

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 21:14 - 21:26

## Visual Description
An animated chart showing the mathematical nature of compounding technical debt. An exponential curve labeled "Debt × (1 + Rate)^Time" grows dramatically upward, visualizing how patching accrues compound costs. A second flat line appears below it — "Regeneration cost (debt resets each cycle)" — showing PDD's fundamentally different trajectory with a subtle sawtooth pattern (small rises then sharp drops as regeneration resets accumulated cruft). A large annotation calls out the CISQ statistic: $1.52 trillion annually in US technical debt costs. The formula is visible on screen, connecting the abstract curve to concrete mathematics.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.04)`, 6 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1300px wide x 550px tall, left margin 310px, top margin 180px
- **X-Axis:** "Time (years)" — labeled at 0, 2, 4, 6, 8, 10, white `#FFFFFF` at 0.5 opacity
- **Y-Axis:** "Cumulative Cost" — no numeric labels (conceptual), white `#FFFFFF` at 0.5 opacity
- **Debt Curve:** `#D9944A` (warm amber), 3px stroke, exponential growth from bottom-left to top-right
  - Formula: y = base × (1.35)^x, normalized to chart area
  - Fill beneath curve: `rgba(217,148,74,0.08)` gradient fading downward
- **Regeneration Line:** `#4A90D9` (cool blue), 3px stroke, nearly flat with subtle sawtooth pattern
  - Sawtooth: Small rises (accumulation within a cycle) followed by sharp drops back to baseline (regeneration resets)
  - Amplitude of sawtooth: ~5% of chart height
  - Flat envelope stays at ~10% of Y-axis
- **Formula Label:** "Debt × (1 + Rate)^Time" — positioned at (1200, 250), `#D9944A` at 0.7 opacity, italic
- **Flat Label:** "Regeneration cost (debt resets each cycle)" — positioned near the flat line at (1100, 620), `#4A90D9` at 0.7 opacity
- **CISQ Callout:** "US tech debt: $1.52 trillion/year" — `#FFFFFF` at 0.5 opacity, 16px, positioned at (960, 820). Source: "CISQ, 2022" — `#94A3B8`, 13px
- **Legend:** Top-right corner, two entries with color swatches

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Axes draw in — X-axis sweeps left-to-right, Y-axis sweeps bottom-to-top. Axis labels fade in
2. **Frame 30-150 (1.0-5.0s):** Debt curve draws from left to right. Starts gentle, then accelerates dramatically upward. Fill beneath the curve fades in progressively as the curve extends. The exponential acceleration is the key visual beat — the curve visibly "takes off" around x=6
3. **Frame 120-160 (4.0-5.33s):** Formula label "Debt × (1 + Rate)^Time" fades in near the curve's steep section, with a thin connector line to the curve
4. **Frame 160-240 (5.33-8.0s):** Regeneration line draws from left to right. The sawtooth pattern is visible — small rises then sharp drops. The contrast with the exponential curve above is stark
5. **Frame 220-260 (7.33-8.67s):** "Regeneration cost" label fades in near the flat line
6. **Frame 260-310 (8.67-10.33s):** CISQ callout slides up from bottom with 15px drift, opacity 0→1
7. **Frame 310-360 (10.33-12.0s):** Hold. The gap between the two curves is visible — the exponential curve dominates the upper portion while the flat line hugs the bottom

### Typography
- Chart Title: Inter, 28px, semi-bold (600), `#FFFFFF`, opacity 0.9
- Axis Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.5
- Formula Label: Inter, 20px, italic, `#D9944A`, opacity 0.7
- Regeneration Label: Inter, 18px, regular (400), `#4A90D9`, opacity 0.7
- CISQ Callout: Inter, 16px, regular (400), `#FFFFFF` at 0.5 opacity
- CISQ Source: Inter, 13px, regular (400), `#94A3B8`

### Easing
- Axis draw: `easeOut(cubic)`
- Debt curve draw: `linear` (time-accurate, but the exponential data itself creates acceleration)
- Fill fade: `easeIn(quad)`
- Formula label fade: `easeOut(quad)`
- Regeneration line draw: `linear`
- Regeneration label fade: `easeOut(quad)`
- CISQ callout slide: `easeOut(cubic)`

## Narration Sync
> "And those costs compound — literally. Technical debt follows a compound interest curve. CISQ puts the US total at one-point-five-two trillion dollars annually. That's not a metaphor. It's the math of accumulation."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Axes */}
  <Sequence from={0} durationInFrames={30}>
    <AnimatedAxis
      xRange={[0, 10]}
      yRange={[0, 100]}
      xLabel="Time (years)"
      yLabel="Cumulative Cost"
      xTicks={[0, 2, 4, 6, 8, 10]}
    />
  </Sequence>

  {/* Exponential Debt Curve */}
  <Sequence from={30} durationInFrames={120}>
    <AnimatedLine
      data={debtCurveData}
      color="#D9944A"
      strokeWidth={3}
      fill="rgba(217,148,74,0.08)"
    />
  </Sequence>

  {/* Formula Label */}
  <Sequence from={120} durationInFrames={40}>
    <AnnotationLabel
      text="Debt × (1 + Rate)^Time"
      x={1200}
      y={250}
      color="#D9944A"
      italic={true}
    />
  </Sequence>

  {/* Regeneration Flat Line */}
  <Sequence from={160} durationInFrames={80}>
    <SawtoothLine
      data={regenerationData}
      color="#4A90D9"
      strokeWidth={3}
      amplitude={5}
    />
  </Sequence>

  {/* Regeneration Label */}
  <Sequence from={220} durationInFrames={40}>
    <AnnotationLabel
      text="Regeneration cost (debt resets each cycle)"
      x={1100}
      y={620}
      color="#4A90D9"
    />
  </Sequence>

  {/* CISQ Callout */}
  <Sequence from={260} durationInFrames={50}>
    <ResearchCallout
      text="US tech debt: $1.52 trillion/year"
      source="CISQ, 2022"
      y={820}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chartArea": {
    "width": 1300,
    "height": 550,
    "marginLeft": 310,
    "marginTop": 180
  },
  "xAxis": { "label": "Time (years)", "range": [0, 10], "ticks": [0, 2, 4, 6, 8, 10] },
  "yAxis": { "label": "Cumulative Cost", "range": [0, 100] },
  "debtCurve": {
    "color": "#D9944A",
    "formula": "base × (1.35)^x",
    "points": [
      { "x": 0, "y": 5 },
      { "x": 1, "y": 7 },
      { "x": 2, "y": 9 },
      { "x": 3, "y": 13 },
      { "x": 4, "y": 17 },
      { "x": 5, "y": 23 },
      { "x": 6, "y": 31 },
      { "x": 7, "y": 42 },
      { "x": 8, "y": 57 },
      { "x": 9, "y": 77 },
      { "x": 10, "y": 100 }
    ],
    "fillColor": "rgba(217,148,74,0.08)"
  },
  "regenerationLine": {
    "color": "#4A90D9",
    "baselineY": 8,
    "sawtoothAmplitude": 5,
    "cycleLength": 1.5
  },
  "cisqCallout": {
    "text": "US tech debt: $1.52 trillion/year",
    "source": "CISQ, 2022"
  }
}
```

---
