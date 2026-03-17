[Remotion]

# Section 4.3: Precision Tradeoff Curve — Tests vs Prompt Precision

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 18:54 - 19:09

## Visual Description

An animated chart reveals the core relationship of Part 4. X-axis: "Number of Tests" (0 to 50+). Y-axis: "Required Prompt Precision" (Low to High). An inverse curve forms — a smooth hyperbola starting high on the left (few tests = high prompt precision needed) and dropping toward the lower-right (many tests = low prompt precision needed).

The curve is the key visual. As it draws, two annotation zones highlight:
- **Left zone (few tests):** A tall amber rectangle highlights the high-precision region. Inside, a miniature prompt document icon is dense with text — many lines, tightly packed. Label: "Detailed prompt required."
- **Right zone (many tests):** A short amber rectangle highlights the low-precision region. Inside, a miniature prompt document is sparse — just a few lines. But surrounding it are many small wall icons (test walls). Label: "Intent is enough."

A slider/cursor animates along the curve from left to right, passing through the transition. As it moves right, prompt icons compress while wall icons multiply — the visual tradeoff made tangible.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Chart area: 1400×700px, centered, with 100px padding

### Chart/Visual Elements

#### Axes
- X-axis: horizontal line at y: 820, `#334155` at 0.4, 2px
  - Label: "Number of Tests →" — Inter, 12px, `#64748B` at 0.5, right-aligned
  - Tick marks: at 0, 10, 20, 30, 40, 50 — 6px tall, `#334155` at 0.3
  - Tick labels: Inter, 10px, `#64748B` at 0.3
- Y-axis: vertical line at x: 260, `#334155` at 0.4, 2px
  - Label: "Required Prompt Precision ↑" — Inter, 12px, `#64748B` at 0.5, rotated -90°
  - Tick labels: "Low", "Medium", "High" — Inter, 10px, `#64748B` at 0.3

#### Inverse Curve
- Path: smooth hyperbola from (260, 180) to (1620, 760)
- Stroke: `#4A90D9` (blue), 3px, with 12px glow at `#4A90D9` at 0.15
- Function approximation: y = 180 + 580 × (1 / (1 + 0.08 × x_test_count))
- Fill below curve: subtle gradient from `#4A90D9` at 0.05 (top) to transparent (bottom)

#### Left Zone (Few Tests)
- Highlight: vertical rectangle x: 280-480, full height, `#D9944A` at 0.04
- Mini prompt icon: 40×60px document at (380, 400), dense horizontal lines (12 lines), `#4A90D9` at 0.5
- Label: "Detailed prompt required" — Inter, 11px, `#D9944A` at 0.6, below icon

#### Right Zone (Many Tests)
- Highlight: vertical rectangle x: 1300-1600, full height, `#5AAA6E` at 0.04
- Mini prompt icon: 40×30px document at (1450, 650), sparse horizontal lines (3 lines), `#4A90D9` at 0.5
- Wall icons: 8 small rectangles surrounding prompt, `#D9944A` at 0.5, 6×20px each
- Label: "Intent is enough" — Inter, 11px, `#5AAA6E` at 0.6, below icon cluster

#### Curve Slider
- Circle: 10px diameter, `#E2E8F0`, with 16px glow at `#4A90D9` at 0.3
- Travels along curve from left to right during animation

#### Title
- "THE PRECISION TRADEOFF" — Inter, 20px, bold (700), `#E2E8F0` at 0.8, centered at y: 80

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background appears. Axes draw in. Title fades in.
2. **Frame 30-60 (1-2s):** Tick marks and labels appear. Axis labels fade in.
3. **Frame 60-180 (2-6s):** Inverse curve draws from left to right with trail glow. Slider follows the drawing edge. Fill gradient follows behind.
4. **Frame 180-240 (6-8s):** Left zone highlight fades in. Dense prompt icon appears. "Detailed prompt required" label.
5. **Frame 240-300 (8-10s):** Right zone highlight fades in. Sparse prompt icon appears surrounded by wall icons. "Intent is enough" label.
6. **Frame 300-390 (10-13s):** Slider animates from left to right along the completed curve. As it passes the midpoint, the left zone dims slightly and the right zone brightens.
7. **Frame 390-450 (13-15s):** Hold on completed chart. Curve pulses gently. Both zones visible.

### Typography
- Title: Inter, 20px, bold (700), `#E2E8F0` at 0.8
- Axis labels: Inter, 12px, `#64748B` at 0.5
- Tick labels: Inter, 10px, `#64748B` at 0.3
- Zone labels: Inter, 11px, respective zone colors at 0.6

### Easing
- Axes draw: `easeOut(cubic)` over 30 frames
- Curve draw: `easeInOut(cubic)` over 120 frames
- Zone fade-in: `easeOut(quad)` over 30 frames
- Slider travel: `easeInOut(cubic)` over 90 frames
- Curve pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "This maps directly to PDD."
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segments: `part4_precision_tradeoff_004`, `part4_precision_tradeoff_005`, `part4_precision_tradeoff_006`

- **26.8s** ("This maps directly to PDD"): Chart axes appear, title visible
- **30.1s** ("With few tests, your prompt needs to specify everything"): Curve drawing through left region, left zone highlighted
- **34.28s** ("Edge cases. Error handling."): Dense prompt icon visible in left zone
- **40.7s** ("With many tests, the prompt only needs to specify intent"): Curve reaches right region, right zone highlighted
- **45.2s** ("The tests handle the constraints"): Wall icons surround sparse prompt, slider at right

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Title */}
    <FadeIn duration={20}>
      <Text text="THE PRECISION TRADEOFF" font="Inter" size={20}
        weight={700} color="#E2E8F0" opacity={0.8}
        x={960} y={80} align="center" />
    </FadeIn>

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        origin={[260, 820]} xLength={1360} yLength={640}
        color="#334155" opacity={0.4} strokeWidth={2}
        xLabel="Number of Tests →" yLabel="Required Prompt Precision ↑"
        xTicks={[0, 10, 20, 30, 40, 50]}
        yTicks={['Low', 'Medium', 'High']}
        drawDuration={30} />
    </Sequence>

    {/* Inverse curve */}
    <Sequence from={60}>
      <InverseCurve
        from={[260, 180]} to={[1620, 760]}
        color="#4A90D9" strokeWidth={3}
        glow={{ blur: 12, opacity: 0.15 }}
        fillGradient={{ from: 'rgba(74,144,217,0.05)', to: 'transparent' }}
        drawDuration={120} />
    </Sequence>

    {/* Left zone — few tests */}
    <Sequence from={180}>
      <FadeIn duration={30}>
        <HighlightZone x={280} width={200} color="#D9944A" opacity={0.04}>
          <DensePromptIcon position={[380, 400]} lines={12}
            color="#4A90D9" opacity={0.5} />
          <Text text="Detailed prompt required" font="Inter" size={11}
            color="#D9944A" opacity={0.6} x={380} y={480} align="center" />
        </HighlightZone>
      </FadeIn>
    </Sequence>

    {/* Right zone — many tests */}
    <Sequence from={240}>
      <FadeIn duration={30}>
        <HighlightZone x={1300} width={300} color="#5AAA6E" opacity={0.04}>
          <SparsePromptIcon position={[1450, 650]} lines={3}
            color="#4A90D9" opacity={0.5} />
          <WallIcons count={8} around={[1450, 650]}
            color="#D9944A" opacity={0.5} size={[6, 20]} />
          <Text text="Intent is enough" font="Inter" size={11}
            color="#5AAA6E" opacity={0.6} x={1450} y={720} align="center" />
        </HighlightZone>
      </FadeIn>
    </Sequence>

    {/* Slider along curve */}
    <Sequence from={300}>
      <CurveSlider
        curvePath={inverseCurvePath}
        size={10} color="#E2E8F0"
        glow={{ blur: 16, color: '#4A90D9', opacity: 0.3 }}
        travelDuration={90} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartType": "inverse_curve",
  "title": "THE PRECISION TRADEOFF",
  "xAxis": {
    "label": "Number of Tests",
    "range": [0, 50],
    "ticks": [0, 10, 20, 30, 40, 50]
  },
  "yAxis": {
    "label": "Required Prompt Precision",
    "range": ["Low", "High"]
  },
  "curve": {
    "type": "inverse_hyperbola",
    "color": "#4A90D9",
    "equation": "y = 180 + 580 * (1 / (1 + 0.08 * x))"
  },
  "zones": [
    { "label": "Detailed prompt required", "range": [0, 10], "color": "#D9944A" },
    { "label": "Intent is enough", "range": [35, 50], "color": "#5AAA6E" }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_004", "part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]
}
```

---
