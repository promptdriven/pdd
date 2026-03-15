[Remotion]

# Section 4.5: Precision Tradeoff Curve — Inverse Relationship Graph

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 19:00 - 19:18

## Visual Description
A full-screen animated graph illustrating the core insight of this section. The X-axis is labeled "Number of Tests" and the Y-axis "Required Prompt Precision". An inverse curve draws from left to right — high precision required with few tests, decreasing sharply as test count grows. A glowing dot animates along the curve, pausing at two key positions: the LEFT extreme (few tests, high precision) where a miniature dense prompt document fans out, and the RIGHT extreme (many tests, low precision) where a miniature minimal prompt sits surrounded by small wall icons. Annotations call out both extremes. The graph communicates: more tests = less prompt precision needed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Chart area gridlines only — horizontal dashed lines at 25%, 50%, 75% Y, `rgba(255,255,255,0.05)`, 1px

### Chart/Visual Elements
- **Chart Area:** 1400px wide x 700px tall, positioned at (260, 100) to (1660, 800)
- **X-Axis:** Horizontal line at Y=800, `#475569`, 2px. Label: "Number of Tests" — Inter 16px semi-bold, `#94A3B8`, centered below axis at Y=850
  - Tick marks at 0, 10, 20, 30, 40, 50 — `#64748B`, 12px
- **Y-Axis:** Vertical line at X=260, `#475569`, 2px. Label: "Required Prompt Precision" — Inter 16px semi-bold, `#94A3B8`, rotated 90° at X=200, vertically centered
  - Tick marks: "Low", "Medium", "High" at 25%, 50%, 75% Y — `#64748B`, 12px
- **Inverse Curve:** Smooth 1/x-style curve from (260, 160) to (1620, 740), stroke width 3px
  - Gradient stroke: starts `#E85D75` (warm red, high precision) → transitions through `#D9944A` (amber, medium) → ends `#5AAA6E` (green, low precision)
  - Subtle glow: `rgba(217,148,74,0.15)` shadow, 8px blur
- **Animated Dot:** 12px diameter circle, `#FFFFFF`, with pulsing glow 20px, travels along the curve
- **Left Callout (few tests):** At curve position (~5 tests, high precision)
  - Mini prompt document icon: 60px x 80px rectangle, `#4A90D9` at 0.3 opacity, filled with 12 faint horizontal "text lines"
  - Label: "50-line prompt\nspecifies everything" — Inter 13px, `#E85D75` at 0.8 opacity, positioned above
  - Connecting dashed line from dot to callout, `rgba(232,93,117,0.3)`, 1px
- **Right Callout (many tests):** At curve position (~45 tests, low precision)
  - Mini prompt document icon: 30px x 40px rectangle, `#4A90D9` at 0.3 opacity, with 3 faint text lines
  - Surrounding wall icons: 8 small amber rectangles (8x20px each), `#D9944A` at 0.4 opacity, arranged in a loose ring around the mini prompt
  - Label: "10-line prompt\ntests handle constraints" — Inter 13px, `#5AAA6E` at 0.8 opacity, positioned above
  - Connecting dashed line from dot to callout, `rgba(90,170,110,0.3)`, 1px
- **Chart Title (top-left of chart area):** "The Precision Tradeoff" — Inter 24px bold, `#FFFFFF` at 0.8 opacity

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Axes draw in — X-axis left-to-right, Y-axis bottom-to-top. Tick marks and labels fade in. Chart title fades in. Grid lines fade in
2. **Frame 40-120 (1.33-4.0s):** Inverse curve draws from left to right with gradient stroke. The curve line progressively reveals, following the mathematical path. Glow follows the drawing tip
3. **Frame 120-150 (4.0-5.0s):** Animated dot appears at the left extreme of the curve (high precision zone). Dot pulses twice. Left callout fades in — mini prompt document with dense lines, label text, connecting line
4. **Frame 150-240 (5.0-8.0s):** Dot travels along the curve from left to right, smoothly decelerating. As it moves, the curve behind it subtly brightens. The transition from red→amber→green is visible along the traversal
5. **Frame 240-300 (8.0-10.0s):** Dot arrives at the right extreme (many tests zone). Dot pulses twice. Right callout fades in — mini prompt with surrounding wall icons, label text, connecting line
6. **Frame 300-420 (10.0-14.0s):** Both callouts visible. A subtle animated arrow sweeps along the curve from left to right, `rgba(255,255,255,0.1)`, indicating the direction of improvement. The arrow carries a label: "Test accumulation" in `#D9944A` at 0.5 opacity, 14px
7. **Frame 420-480 (14.0-16.0s):** The region under the curve fills with a subtle gradient — `rgba(90,170,110,0.05)` (green tint), suggesting the "gained simplicity" area
8. **Frame 480-540 (16.0-18.0s):** Hold at final state. All elements visible. Dot rests at right extreme

### Typography
- Chart Title: Inter, 24px, bold (700), `#FFFFFF` at 0.8 opacity
- Axis Labels: Inter, 16px, semi-bold (600), `#94A3B8`
- Tick Labels: JetBrains Mono, 12px, regular (400), `#64748B`
- Callout Labels: Inter, 13px, regular (400), respective zone color at 0.8 opacity
- Arrow Label: Inter, 14px, italic (400), `#D9944A` at 0.5 opacity

### Easing
- Axis draw: `easeOut(cubic)`
- Curve draw: `easeInOut(quad)`
- Dot pulse: `easeInOut(sine)`
- Dot traversal: `easeInOut(cubic)` (slow at extremes, faster in middle)
- Callout fade-in: `easeOut(quad)`
- Arrow sweep: `easeInOut(quad)`
- Under-curve fill: `easeIn(quad)`

## Narration Sync
> "This maps directly to PDD."
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Axes and Grid */}
  <Sequence from={0} durationInFrames={40}>
    <ChartAxes
      xLabel="Number of Tests"
      yLabel="Required Prompt Precision"
      xTicks={[0, 10, 20, 30, 40, 50]}
      yTicks={["Low", "Medium", "High"]}
      chartArea={{ x: 260, y: 100, width: 1400, height: 700 }}
    />
    <ChartTitle text="The Precision Tradeoff" x={280} y={80} />
  </Sequence>

  {/* Inverse Curve */}
  <Sequence from={40} durationInFrames={80}>
    <InverseCurve
      data={curvePoints}
      strokeWidth={3}
      gradientColors={["#E85D75", "#D9944A", "#5AAA6E"]}
      glowColor="rgba(217,148,74,0.15)"
    />
  </Sequence>

  {/* Animated Dot — Left Pause */}
  <Sequence from={120} durationInFrames={30}>
    <CurveDot position="start" pulseCount={2} size={12} />
    <FadeIn>
      <LeftCallout
        promptLines={12}
        label={"50-line prompt\nspecifies everything"}
        labelColor="#E85D75"
      />
    </FadeIn>
  </Sequence>

  {/* Dot Traversal */}
  <Sequence from={150} durationInFrames={90}>
    <CurveDotTraversal
      from="start"
      to="end"
      curve={curvePoints}
      size={12}
    />
  </Sequence>

  {/* Animated Dot — Right Pause */}
  <Sequence from={240} durationInFrames={60}>
    <CurveDot position="end" pulseCount={2} size={12} />
    <FadeIn>
      <RightCallout
        promptLines={3}
        wallCount={8}
        label={"10-line prompt\ntests handle constraints"}
        labelColor="#5AAA6E"
      />
    </FadeIn>
  </Sequence>

  {/* Direction Arrow */}
  <Sequence from={300} durationInFrames={120}>
    <CurveArrow
      curve={curvePoints}
      label="Test accumulation"
      arrowColor="rgba(255,255,255,0.1)"
      labelColor="#D9944A"
    />
  </Sequence>

  {/* Under-Curve Fill */}
  <Sequence from={420} durationInFrames={60}>
    <UnderCurveFill color="rgba(90,170,110,0.05)" curve={curvePoints} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chartArea": {
    "x": 260,
    "y": 100,
    "width": 1400,
    "height": 700
  },
  "axes": {
    "color": "#475569",
    "strokeWidth": 2,
    "xLabel": "Number of Tests",
    "yLabel": "Required Prompt Precision",
    "xTicks": [0, 10, 20, 30, 40, 50],
    "yTicks": ["Low", "Medium", "High"]
  },
  "curve": {
    "type": "inverse",
    "formula": "precision = k / (tests + c)",
    "points": [
      { "tests": 0, "precision": 0.95 },
      { "tests": 2, "precision": 0.88 },
      { "tests": 5, "precision": 0.75 },
      { "tests": 10, "precision": 0.55 },
      { "tests": 15, "precision": 0.40 },
      { "tests": 20, "precision": 0.30 },
      { "tests": 30, "precision": 0.20 },
      { "tests": 40, "precision": 0.14 },
      { "tests": 50, "precision": 0.10 }
    ],
    "strokeWidth": 3,
    "gradientColors": ["#E85D75", "#D9944A", "#5AAA6E"],
    "glowColor": "rgba(217,148,74,0.15)"
  },
  "leftCallout": {
    "testCount": 3,
    "precision": "High",
    "promptLines": 50,
    "label": "50-line prompt\nspecifies everything",
    "color": "#E85D75"
  },
  "rightCallout": {
    "testCount": 47,
    "precision": "Low",
    "promptLines": 10,
    "wallIcons": 8,
    "label": "10-line prompt\ntests handle constraints",
    "color": "#5AAA6E"
  }
}
```

---
