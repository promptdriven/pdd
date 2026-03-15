[Remotion]

# Section 5.4: Diverging Cost Curves — Patching vs PDD Over Time

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 21:26 - 21:38

## Visual Description
Two curves diverge dramatically over time, making the central economic argument of the entire video viscerally visible. The "Patching" curve grows exponentially upward (cost), while the "PDD" curve stays flat (cost resets each cycle). The gap between them widens with each passing year — a visual representation of compound costs vs. compound returns. Annotation callouts highlight the key insight: patching accrues compound costs while each test constrains every future generation. The widening gap is the emotional climax of the section — this is "the math of everything."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.04)`, 5 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1300px wide x 550px tall, left margin 310px, top margin 180px
- **X-Axis:** "Time" — labeled at Year 1, Year 3, Year 5, Year 7, Year 10, white `#FFFFFF` at 0.5 opacity
- **Y-Axis:** "Total Cost of Ownership" — no numeric labels, white `#FFFFFF` at 0.5 opacity
- **Patching Curve:** `#D9944A` (warm amber), 3.5px stroke, exponential upward
  - Shaded area beneath: `rgba(217,148,74,0.06)`, gradient fading down
  - Small annotation markers along curve: "patch", "debt", "patch", "more debt" in `#D9944A` at 0.3 opacity, 11px
- **PDD Curve:** `#4A90D9` (cool blue), 3.5px stroke, flat with slight downward trend
  - Subtle green glow along the line: `rgba(90,170,110,0.15)`, 8px blur, representing value accumulation
  - Small upward tick marks at regular intervals representing tests added, `#5AAA6E` at 0.4 opacity, 4px tall
- **Gap Region:** Between the two curves, filled with `rgba(255,255,255,0.02)` and subtle vertical hash marks to emphasize the divergence
- **Gap Label:** "The compounding gap" — `#FFFFFF` at 0.6 opacity, 18px, positioned midway in the gap at x=75% of chart width, with a vertical double-arrow connecting the two curves
- **Annotation — Patching:** "Each patch adds debt. Debt generates more debt." — `#D9944A` at 0.5 opacity, 14px, positioned near curve at (1350, 220)
- **Annotation — PDD:** "Each test constrains all future generations." — `#4A90D9` at 0.5 opacity, 14px, positioned near flat line at (1350, 600)

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Axes draw in. Axis labels fade in
2. **Frame 30-60 (1.0-2.0s):** Both curves begin drawing simultaneously from the left. They start at the same Y value — costs are equal initially
3. **Frame 60-180 (2.0-6.0s):** Curves diverge. Patching curve accelerates upward; PDD curve stays flat. The gap widens visibly. Small "patch" and "debt" markers appear along the amber curve (staggered, one every 30 frames). Green tick marks appear along the blue curve
4. **Frame 180-230 (6.0-7.67s):** Gap region fills in between the two curves. The double-arrow and "The compounding gap" label fade in
5. **Frame 230-280 (7.67-9.33s):** Annotation for patching slides in (right side). Then annotation for PDD slides in (right side, 20-frame stagger)
6. **Frame 280-320 (9.33-10.67s):** Brief pulse — patching curve glows amber, PDD curve glows blue, emphasizing the contrast
7. **Frame 320-360 (10.67-12.0s):** Hold at final state. The visual gap dominates the screen

### Typography
- Axis Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.5
- Curve Labels: Inter, 16px, semi-bold (600), respective colors, opacity 0.8
- Gap Label: Inter, 18px, semi-bold (600), `#FFFFFF`, opacity 0.6
- Annotations: Inter, 14px, regular (400), respective colors, opacity 0.5
- Marker Text: Inter, 11px, regular (400), `#D9944A`, opacity 0.3

### Easing
- Axis draw: `easeOut(cubic)`
- Curve draw: `linear` (both curves)
- Gap fill: `easeIn(quad)`
- Gap label fade: `easeOut(quad)`
- Annotations slide: `easeOut(cubic)`
- Pulse: `easeInOut(sine)`

## Narration Sync
> "Patching accrues compound costs. Each patch adds debt. Debt generates more debt."
> "But the mold works the other way. Each test you write constrains every future generation. Today's. Next month's. Next year's. Tests accrue compound returns."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Axes */}
  <Sequence from={0} durationInFrames={30}>
    <AnimatedAxis
      xRange={[0, 10]}
      xLabel="Time"
      yLabel="Total Cost of Ownership"
      xTicks={["Year 1", "Year 3", "Year 5", "Year 7", "Year 10"]}
    />
  </Sequence>

  {/* Both Curves */}
  <Sequence from={30} durationInFrames={150}>
    <AnimatedLine data={patchingCurveData} color="#D9944A" strokeWidth={3.5} fill="rgba(217,148,74,0.06)" />
    <AnimatedLine data={pddCurveData} color="#4A90D9" strokeWidth={3.5} />
    <CurveMarkers curve="patching" labels={["patch", "debt", "patch", "more debt"]} color="#D9944A" />
    <TestTickMarks curve="pdd" color="#5AAA6E" />
  </Sequence>

  {/* Gap */}
  <Sequence from={180} durationInFrames={50}>
    <GapRegion upperCurve={patchingCurveData} lowerCurve={pddCurveData} fill="rgba(255,255,255,0.02)" />
    <GapLabel text="The compounding gap" x={1100} />
  </Sequence>

  {/* Annotations */}
  <Sequence from={230} durationInFrames={50}>
    <AnnotationLabel text="Each patch adds debt. Debt generates more debt." color="#D9944A" x={1350} y={220} />
    <Sequence from={20}>
      <AnnotationLabel text="Each test constrains all future generations." color="#4A90D9" x={1350} y={600} />
    </Sequence>
  </Sequence>

  {/* Pulse */}
  <Sequence from={280} durationInFrames={40}>
    <CurvePulse curves={["patching", "pdd"]} />
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
  "xAxis": { "label": "Time", "ticks": ["Year 1", "Year 3", "Year 5", "Year 7", "Year 10"] },
  "yAxis": { "label": "Total Cost of Ownership" },
  "patchingCurve": {
    "color": "#D9944A",
    "strokeWidth": 3.5,
    "points": [
      { "x": 0, "y": 10 },
      { "x": 1, "y": 14 },
      { "x": 2, "y": 19 },
      { "x": 3, "y": 26 },
      { "x": 4, "y": 35 },
      { "x": 5, "y": 44 },
      { "x": 6, "y": 55 },
      { "x": 7, "y": 68 },
      { "x": 8, "y": 82 },
      { "x": 9, "y": 92 },
      { "x": 10, "y": 100 }
    ]
  },
  "pddCurve": {
    "color": "#4A90D9",
    "strokeWidth": 3.5,
    "points": [
      { "x": 0, "y": 10 },
      { "x": 1, "y": 10 },
      { "x": 2, "y": 9 },
      { "x": 3, "y": 9 },
      { "x": 4, "y": 8 },
      { "x": 5, "y": 8 },
      { "x": 6, "y": 7 },
      { "x": 7, "y": 7 },
      { "x": 8, "y": 7 },
      { "x": 9, "y": 6 },
      { "x": 10, "y": 6 }
    ]
  }
}
```

---
