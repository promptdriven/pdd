[Remotion]

# Section 4.3: Precision Tradeoff Curve — Inverse Relationship Graph

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 0:24 – 0:42

## Visual Description
A full-screen animated graph showing the inverse relationship between number of tests and required prompt precision. The X-axis represents "Number of Tests" (0–50), the Y-axis represents "Required Prompt Precision" (High to Low). An inverse curve draws from left to right — steep drop initially, flattening as tests accumulate. A dot travels along the curve, pausing at two key extremes: far left (few tests, high precision needed) where a dense 50-line prompt thumbnail appears, and far right (many tests, low precision needed) where a minimal 10-line prompt thumbnail appears surrounded by test wall icons. The curve uses a gradient from red (high precision) through amber to green (low precision), making the tradeoff viscerally clear.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: Horizontal, `rgba(255,255,255,0.04)`, 5 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1200px wide × 550px tall, left margin 360px, top margin 200px
- **X-Axis:** "Number of Tests" — labeled at 0, 10, 20, 30, 40, 50, white `#FFFFFF` at 0.5 opacity
- **Y-Axis:** "Required Prompt Precision" — labeled "High" at top, "Low" at bottom, white `#FFFFFF` at 0.5 opacity
- **Inverse Curve:** 3px stroke with gradient:
  - Left portion (0–15 tests): `#EF4444` (red — high precision required)
  - Middle portion (15–30 tests): `#D9944A` (amber — moderate)
  - Right portion (30–50 tests): `#5AAA6E` (green — low precision, tests do the work)
  - Fill beneath curve: matching gradient at 0.06 opacity, fading downward
  - Mathematical shape: y = 1 / (0.05x + 0.2), normalized to chart area
- **Traveling dot:** 10px circle, white `#FFFFFF` with subtle glow, follows the curve left→right
- **Left extreme callout (few tests):**
  - Position: Near curve at x≈5 tests, y≈high
  - Thumbnail: Mini prompt document, 80×120px, dense lines (representing 50-line prompt)
  - Label: "50-line prompt" — `#EF4444`, 14px
  - Sublabel: "Must specify everything" — `#94A3B8`, 12px
- **Right extreme callout (many tests):**
  - Position: Near curve at x≈45 tests, y≈low
  - Thumbnail: Mini prompt document, 80×50px (shorter), surrounded by 8 small wall icons
  - Label: "10-line prompt" — `#5AAA6E`, 14px
  - Sublabel: "Tests handle constraints" — `#94A3B8`, 12px
  - Wall icons: 8 small amber rectangles (12×8px each), `#D9944A` at 0.5 opacity, surrounding the prompt thumbnail

### Animation Sequence
1. **Frame 0–30 (0–1.0s):** Axes draw in — X-axis sweeps left-to-right, Y-axis sweeps bottom-to-top. Axis labels and tick marks fade in.
2. **Frame 30–150 (1.0–5.0s):** Inverse curve draws from left to right. The gradient color shifts as the line progresses — starting red, transitioning to amber, ending green. Fill beneath fades in progressively.
3. **Frame 150–240 (5.0–8.0s):** Traveling dot appears at far-left of curve. Pauses for 30 frames. Left extreme callout fades in — thumbnail of dense prompt, "50-line prompt" label. Connector line (thin, dashed, `#EF4444` at 0.3 opacity) links callout to dot position.
4. **Frame 240–360 (8.0–12.0s):** Dot travels along curve from left to right. Speed: slow at first (steep descent is dramatic), then accelerating as the curve flattens. The visual sensation: the curve "runs out of precision to demand."
5. **Frame 360–450 (12.0–15.0s):** Dot reaches far-right of curve. Pauses for 30 frames. Right extreme callout fades in — small prompt thumbnail surrounded by wall icons, "10-line prompt" label. Connector line (`#5AAA6E` at 0.3 opacity).
6. **Frame 450–510 (15.0–17.0s):** Both callouts visible. The gap between them — the height difference on the curve — is the visual punchline. A thin horizontal annotation line connects both Y positions, labeled "Precision saved by tests" in `#FFFFFF` at 0.4 opacity, 14px.
7. **Frame 510–540 (17.0–18.0s):** Hold. Ambient pulse on the curve fill.

### Typography
- Chart Title: (none — narration carries it)
- Axis Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.5
- Tick Labels: Inter, 13px, regular (400), `#FFFFFF`, opacity 0.4
- Callout Labels: Inter SemiBold, 14px, respective colors
- Callout Sublabels: Inter Regular, 12px, `#94A3B8`
- Annotation: Inter Regular, 14px, `#FFFFFF` at 0.4 opacity

### Easing
- Axis draw: `easeOutCubic`
- Curve draw: `linear` (constant reveal speed; the math creates visual acceleration)
- Dot travel: `easeInOutCubic` (slow at extremes, faster through middle)
- Callout fade: `easeOutQuad`
- Connector line: `easeOutQuad`
- Annotation fade: `easeOutQuad`

## Narration Sync
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."

> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Axes */}
    <Sequence from={0} durationInFrames={30}>
      <AnimatedAxis
        xRange={[0, 50]}
        yRange={[0, 100]}
        xLabel="Number of Tests"
        yLabel="Required Prompt Precision"
        xTicks={[0, 10, 20, 30, 40, 50]}
        yLabels={{ top: "High", bottom: "Low" }}
      />
    </Sequence>

    {/* Inverse Curve with gradient */}
    <Sequence from={30} durationInFrames={120}>
      <GradientLine
        data={inverseCurveData}
        gradient={["#EF4444", "#D9944A", "#5AAA6E"]}
        strokeWidth={3}
        fillOpacity={0.06}
      />
    </Sequence>

    {/* Traveling dot + left callout */}
    <Sequence from={150} durationInFrames={90}>
      <TravelingDot data={inverseCurveData} position={0} />
      <Callout
        label="50-line prompt"
        sublabel="Must specify everything"
        color="#EF4444"
        thumbnail="dense-prompt"
        position="left"
      />
    </Sequence>

    {/* Dot traversal */}
    <Sequence from={240} durationInFrames={120}>
      <TravelingDot data={inverseCurveData} animate={{ from: 0, to: 1 }} />
    </Sequence>

    {/* Right callout */}
    <Sequence from={360} durationInFrames={90}>
      <TravelingDot data={inverseCurveData} position={1} />
      <Callout
        label="10-line prompt"
        sublabel="Tests handle constraints"
        color="#5AAA6E"
        thumbnail="minimal-prompt-with-walls"
        wallIcons={8}
        position="right"
      />
    </Sequence>

    {/* Annotation */}
    <Sequence from={450} durationInFrames={60}>
      <AnnotationLine
        label="Precision saved by tests"
        color="#FFFFFF"
        opacity={0.4}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chartArea": {
    "width": 1200,
    "height": 550,
    "marginLeft": 360,
    "marginTop": 200
  },
  "xAxis": { "label": "Number of Tests", "range": [0, 50], "ticks": [0, 10, 20, 30, 40, 50] },
  "yAxis": { "label": "Required Prompt Precision", "labels": { "top": "High", "bottom": "Low" } },
  "inverseCurve": {
    "formula": "1 / (0.05x + 0.2)",
    "gradient": ["#EF4444", "#D9944A", "#5AAA6E"],
    "points": [
      { "x": 0, "y": 100 },
      { "x": 5, "y": 80 },
      { "x": 10, "y": 67 },
      { "x": 15, "y": 57 },
      { "x": 20, "y": 50 },
      { "x": 25, "y": 44 },
      { "x": 30, "y": 40 },
      { "x": 35, "y": 36 },
      { "x": 40, "y": 33 },
      { "x": 45, "y": 31 },
      { "x": 50, "y": 29 }
    ]
  },
  "callouts": {
    "left": {
      "label": "50-line prompt",
      "sublabel": "Must specify everything",
      "color": "#EF4444",
      "testCount": 3
    },
    "right": {
      "label": "10-line prompt",
      "sublabel": "Tests handle constraints",
      "color": "#5AAA6E",
      "testCount": 47,
      "wallIcons": 8
    }
  }
}
```

---
