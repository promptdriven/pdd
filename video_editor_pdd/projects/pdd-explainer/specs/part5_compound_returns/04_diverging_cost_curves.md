[Remotion]

# Section 5.4: Diverging Cost Curves — Patching vs. PDD Over Time

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 0:42 - 1:02

## Visual Description
The core economic argument of the entire video, visualized. Two cost curves diverge dramatically over a shared time axis:

- **"Patching" (amber):** An exponential curve climbing steeply upward — each year costs more than the last because patches accumulate debt that generates more debt.
- **"PDD" (teal):** A nearly flat line with periodic small sawtooth bumps — each regeneration cycle resets cost to near-zero. Tests constrain every future generation, so investment compounds in your favor.

The gap between the two curves fills with a gradient that widens dramatically, making the divergence visceral. Text callouts appear at key moments: "Each patch adds debt" near the rising amber curve, and "Each test constrains forever" near the flat teal line.

A final beat zooms the camera slightly into the widening gap with a label: "Over time, it's everything."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal dashed at `#1E293B` opacity `0.06`, 4 lines evenly spaced

### Chart/Visual Elements

#### Axes
- X-axis: "Years" — 0 to 10, labeled at each year
  - Color: `#475569` opacity `0.6`, Inter 12px
- Y-axis: "Cumulative Cost" — 0 to max, no numeric labels (conceptual scale)
  - Color: `#475569` opacity `0.6`, Inter 12px
- Axis lines: `#334155` opacity `0.3`, 1px

#### Patching Curve
- Color: `#D9944A` (warm amber), 3.5px stroke
- Shape: exponential — starts at `(0, 2)`, grows to `(10, 90)` (fills most of Y-axis)
- Data: `(0, 2), (1, 3), (2, 4.5), (3, 7), (4, 11), (5, 17), (6, 26), (7, 39), (8, 55), (9, 72), (10, 90)`
- Glow: `6px`, `#D9944A` opacity `0.12`
- Label: "Patching" — Inter, 18px, bold, `#D9944A`, positioned above curve endpoint

#### PDD Curve
- Color: `#4A90D9` (steel blue), 3.5px stroke
- Shape: flat with small sawtooth — cost resets each cycle
- Data: `(0, 2), (1, 3.5), (1.5, 2.2), (3, 3.8), (3.5, 2.3), (5, 3.9), (5.5, 2.2), (7, 3.7), (7.5, 2.1), (9, 3.6), (10, 4.0)`
- Each sawtooth represents a regeneration: cost builds slightly, then resets
- Label: "PDD" — Inter, 18px, bold, `#4A90D9`, positioned at line end

#### Divergence Fill
- Gradient fill between the two curves
- Upper edge: `#D9944A` opacity `0.06`
- Lower edge: `#4A90D9` opacity `0.03`
- Expands as curves diverge

#### Callout Annotations
- **"Each patch adds debt"** — Inter, 13px, italic, `#D9944A` opacity `0.8`, with a small arrow pointing to the steep amber section around year 6
- **"Each test constrains forever"** — Inter, 13px, italic, `#4A90D9` opacity `0.8`, with a small arrow pointing to the flat teal line around year 6
- **"Over time, it's everything."** — Inter, 20px, bold, `#E2E8F0`, centered in the gap at year 9, appears last

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Axes and grid fade in. Both curves begin drawing from year 0 where they start at the same point.
2. **Frame 45-150 (1.5-5s):** Both curves draw simultaneously, left to right. Through years 0-4, they begin to separate. The amber line starts pulling upward.
3. **Frame 150-300 (5-10s):** Years 5-8. The divergence becomes dramatic. Amber shoots upward; teal stays flat with its periodic resets. Gradient fill animates between the curves.
4. **Frame 300-360 (10-12s):** Curves reach year 10. Labels "Patching" and "PDD" appear at endpoints. The gap is enormous.
5. **Frame 360-420 (12-14s):** Callout annotations fade in: "Each patch adds debt" near amber, "Each test constrains forever" near teal.
6. **Frame 420-510 (14-17s):** Slow zoom-in (`scale 1.0→1.08`) focusing on the widening gap at years 8-10. "Over time, it's everything." fades in centered in the gap.
7. **Frame 510-600 (17-20s):** Hold at zoomed position. The visual weight of the divergence settles.

### Typography
- Curve labels: Inter, 18px, bold (700), respective curve colors
- Annotation callouts: Inter, 13px, italic (400i), respective curve colors at `0.8`
- Impact text: Inter, 20px, bold (700), `#E2E8F0`
- Axis labels: Inter, 12px, regular (400), `#475569` opacity `0.6`

### Easing
- Curve draw: `easeInOutCubic` over draw duration
- Divergence fill: `easeInQuad` — fills slowly at first, faster as gap widens
- Annotations fade: `easeOutQuad` over 25 frames
- Impact text: `easeOutCubic` over 30 frames with slight scale `0.9→1.0`
- Zoom: `easeInOutCubic` over 90 frames

## Narration Sync
> "Patching accrues compound costs. Each patch adds debt. Debt generates more debt."
> "But the mold works the other way. Each test you write constrains every future generation. Today's. Next month's. Next year's. Tests accrue compound returns."
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Axes and grid */}
    <Sequence from={0}>
      <FadeIn durationInFrames={30}>
        <ChartAxes
          xRange={[0, 10]} yRange={[0, 100]}
          xLabel="Years" yLabel="Cumulative Cost"
          gridColor="#1E293B" gridOpacity={0.06}
          axisColor="#334155" labelColor="#475569" />
      </FadeIn>
    </Sequence>

    {/* Patching curve (amber, exponential) */}
    <Sequence from={45}>
      <AnimatedLine
        data={[
          [0, 2], [1, 3], [2, 4.5], [3, 7], [4, 11],
          [5, 17], [6, 26], [7, 39], [8, 55], [9, 72], [10, 90]
        ]}
        color="#D9944A" strokeWidth={3.5}
        glowRadius={6} glowOpacity={0.12}
        drawDuration={255} easing="easeInOutCubic"
        label="Patching" labelColor="#D9944A" labelSize={18} />
    </Sequence>

    {/* PDD curve (teal, flat sawtooth) */}
    <Sequence from={45}>
      <AnimatedLine
        data={[
          [0, 2], [1, 3.5], [1.5, 2.2], [3, 3.8], [3.5, 2.3],
          [5, 3.9], [5.5, 2.2], [7, 3.7], [7.5, 2.1], [9, 3.6], [10, 4.0]
        ]}
        color="#4A90D9" strokeWidth={3.5}
        drawDuration={255} easing="easeInOutCubic"
        label="PDD" labelColor="#4A90D9" labelSize={18} />
    </Sequence>

    {/* Divergence gradient fill */}
    <Sequence from={150}>
      <FillArea
        upperLine="patching_curve" lowerLine="pdd_curve"
        gradientTop={{ color: "#D9944A", opacity: 0.06 }}
        gradientBottom={{ color: "#4A90D9", opacity: 0.03 }}
        fillDuration={150} easing="easeInQuad" />
    </Sequence>

    {/* Annotation callouts */}
    <Sequence from={360}>
      <FadeIn durationInFrames={25}>
        <Annotation text="Each patch adds debt" font="Inter"
          size={13} style="italic" color="#D9944A" opacity={0.8}
          anchorX={6} anchorY={26} arrowDirection="up" />
      </FadeIn>
    </Sequence>
    <Sequence from={385}>
      <FadeIn durationInFrames={25}>
        <Annotation text="Each test constrains forever" font="Inter"
          size={13} style="italic" color="#4A90D9" opacity={0.8}
          anchorX={6} anchorY={3.8} arrowDirection="down" />
      </FadeIn>
    </Sequence>

    {/* Zoom and impact text */}
    <Sequence from={420}>
      <ZoomIn fromScale={1.0} toScale={1.08}
        focusX={0.75} focusY={0.5}
        durationInFrames={90} easing="easeInOutCubic">
        <Sequence from={30}>
          <ScaleAndFade fromScale={0.9} toScale={1.0}
            durationInFrames={30} easing="easeOutCubic">
            <Text text="Over time, it's everything."
              font="Inter" size={20} weight={700} color="#E2E8F0"
              align="center" y={0} />
          </ScaleAndFade>
        </Sequence>
      </ZoomIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "diverging_line_chart",
  "xAxis": { "label": "Years", "range": [0, 10] },
  "yAxis": { "label": "Cumulative Cost", "range": [0, 100] },
  "series": [
    {
      "id": "patching_curve",
      "label": "Patching",
      "color": "#D9944A",
      "style": "solid",
      "data": [[0, 2], [1, 3], [2, 4.5], [3, 7], [4, 11], [5, 17], [6, 26], [7, 39], [8, 55], [9, 72], [10, 90]]
    },
    {
      "id": "pdd_curve",
      "label": "PDD",
      "color": "#4A90D9",
      "style": "solid",
      "data": [[0, 2], [1, 3.5], [1.5, 2.2], [3, 3.8], [3.5, 2.3], [5, 3.9], [5.5, 2.2], [7, 3.7], [7.5, 2.1], [9, 3.6], [10, 4.0]]
    }
  ],
  "annotations": [
    { "text": "Each patch adds debt", "anchorYear": 6, "target": "patching_curve" },
    { "text": "Each test constrains forever", "anchorYear": 6, "target": "pdd_curve" }
  ],
  "impactText": "Over time, it's everything.",
  "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005", "part5_compound_returns_006"]
}
```
