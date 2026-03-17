[Remotion]

# Section 4.5: Precision Tradeoff Curve — Tests vs Prompt Detail

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 19:08 - 19:24

## Visual Description

An animated graph that is the centerpiece of Part 4. The X-axis represents "Number of Tests" (0 to 50+). The Y-axis represents "Required Prompt Precision" (low to high). An inverse curve draws itself — a smooth hyperbola that starts high on the left (few tests = high prompt precision needed) and descends to the right (many tests = low prompt precision needed).

Two annotated points on the curve are highlighted:

**Left point** (few tests): A callout box shows a dense, 50-line prompt file — `parser_v1.prompt` — with tightly packed text. The prompt glows red-amber, signaling stress and over-specification. Label: "5 tests → 50-line prompt."

**Right point** (many tests): A callout box shows a minimal, 10-line prompt — `parser_v2.prompt` — with generous whitespace. Below it, a terminal snippet shows `pdd test parser` with 47 green checkmarks. The prompt glows calm blue-green. Label: "47 tests → 10-line prompt."

An animated slider dot travels along the curve from left to right, showing the tradeoff in real-time. As it moves right, the prompt preview shrinks and test walls multiply.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: horizontal at 5 intervals on Y, `#1E293B` at 0.06; vertical at 10-test intervals on X, `#1E293B` at 0.06

### Chart/Visual Elements

#### Axes
- X-axis: "Number of Tests" — 0 to 50, positioned at y: 820, `#475569` at 0.5, 2px
  - Tick labels at 0, 5, 10, 20, 30, 40, 50 — Inter, 11px, `#64748B` at 0.4
  - Axis label: "Number of Tests" — Inter, 13px, `#64748B` at 0.5, at y: 870
- Y-axis: "Required Prompt Precision" — low to high, positioned at x: 180, `#475569` at 0.5, 2px
  - Qualitative labels: "Low", "Medium", "High", "Extreme" — Inter, 11px, `#64748B` at 0.4
  - Axis label: "Required Prompt Precision" — Inter, 13px, `#64748B` at 0.5, rotated 90°, at x: 100

#### Inverse Curve
- Color: `#E2E8F0` at 0.8, 3px stroke
- Shape: hyperbola y = k / (x + c) — high at x=0, asymptotically approaching low at x=50
- Glow trail: 8px Gaussian blur, `#E2E8F0` at 0.08
- Data points: smooth bezier through [(0, 95), (5, 80), (10, 55), (20, 35), (30, 22), (40, 15), (50, 10)]

#### Shaded Regions
- "Danger zone" (top-left quadrant): `#EF4444` at 0.03, above curve for x < 15
  - Faint label: "Over-specified" — Inter, 10px, `#EF4444` at 0.2
- "Sweet spot" (bottom-right quadrant): `#22C55E` at 0.03, below curve for x > 30
  - Faint label: "Tests handle constraints" — Inter, 10px, `#22C55E` at 0.2

#### Slider Dot
- 10px circle, `#E2E8F0` at 1.0, with 20px glow at 0.2
- Travels along the curve from left to right over 120 frames
- Current position updates the prompt preview and test count dynamically

#### Left Callout — Few Tests (x: 5 on chart)
- Connected to curve point with thin leader line, `#475569` at 0.3
- Callout box at (380, 180), 280x200px
  - Background: `#1E293B` at 0.5, 1px border `#334155`
  - File header: `parser_v1.prompt` — JetBrains Mono, 10px, `#D9944A` at 0.6
  - Content: 8 visible lines of dense pseudo-prompt text, tightly packed
    - JetBrains Mono, 8px, `#94A3B8` at 0.4
    - Lines like "Must validate: null, empty, whitespace, unicode..."
  - Line count badge: "50 lines" — Inter, 9px, `#EF4444` at 0.5, bottom-right
  - Subtle amber/red glow around callout: `#EF4444` at 0.06, 15px blur
- Label below: "5 tests → 50-line prompt" — Inter, 12px, `#D9944A` at 0.6

#### Right Callout — Many Tests (x: 47 on chart)
- Connected to curve point with thin leader line, `#475569` at 0.3
- Callout box at (1350, 500), 280x180px
  - Background: `#1E293B` at 0.5, 1px border `#334155`
  - File header: `parser_v2.prompt` — JetBrains Mono, 10px, `#22C55E` at 0.6
  - Content: 4 visible lines with generous whitespace
    - JetBrains Mono, 8px, `#94A3B8` at 0.4
    - Lines like "Parse input according to RFC 7159." / "Return structured AST."
  - Line count badge: "10 lines" — Inter, 9px, `#22C55E` at 0.5, bottom-right
  - Subtle green glow around callout: `#22C55E` at 0.06, 15px blur
- Terminal snippet below callout:
  - `$ pdd test parser` — JetBrains Mono, 9px, `#94A3B8` at 0.4
  - `47/47 passing ✓` — JetBrains Mono, 9px, `#22C55E` at 0.6
- Label below: "47 tests → 10-line prompt" — Inter, 12px, `#22C55E` at 0.6

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Axes draw in. Grid lines appear. Axis labels fade in.
2. **Frame 40-120 (1.33-4s):** Curve draws from left to right — starts high, descends. Glow trail follows.
3. **Frame 120-160 (4-5.33s):** Shaded regions fade in — red danger zone (top-left), green sweet spot (bottom-right).
4. **Frame 160-220 (5.33-7.33s):** Left callout appears. Leader line draws. Callout box fades in. Dense prompt text scrolls briefly. "50 lines" badge appears. "5 tests → 50-line prompt" label fades in.
5. **Frame 220-300 (7.33-10s):** Slider dot begins traveling along curve from left to right. As it passes the midpoint, the right callout begins appearing.
6. **Frame 300-370 (10-12.33s):** Right callout fully visible. Minimal prompt, terminal output with green checkmarks. "10 lines" badge. "47 tests → 10-line prompt" label appears.
7. **Frame 370-420 (12.33-14s):** Slider dot reaches the right side. Both callouts visible simultaneously. The contrast is the argument.
8. **Frame 420-480 (14-16s):** Hold. Curve pulses gently. Both callouts breathe. The inverse relationship is self-evident.

### Typography
- Axis labels: Inter, 13px, `#64748B` at 0.5
- Tick labels: Inter, 11px, `#64748B` at 0.4
- File headers: JetBrains Mono, 10px, respective colors at 0.6
- Prompt text: JetBrains Mono, 8px, `#94A3B8` at 0.4
- Line count badges: Inter, 9px, respective colors at 0.5
- Callout labels: Inter, 12px, respective colors at 0.6
- Zone labels: Inter, 10px, respective colors at 0.2

### Easing
- Axes draw: `easeOut(cubic)` over 30 frames
- Curve draw: `easeInOut(cubic)` over 80 frames
- Region fade: `easeOut(quad)` over 30 frames
- Callout appearance: `easeOut(cubic)` over 25 frames
- Slider dot travel: `easeInOut(cubic)` over 120 frames
- Curve pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segment: `part4_005`

- **19:08** ("With few tests"): Curve visible, slider at left, dense prompt callout appears
- **19:12** ("Edge cases. Error handling."): Dense prompt text scrolling, red glow visible
- **19:16** ("With many tests"): Slider moving right, right callout appearing
- **19:20** ("The tests handle the constraints"): Minimal prompt + 47 tests visible, green glow

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Chart grid and axes */}
    <Sequence from={0}>
      <ChartAxes
        xRange={[0, 50]} yRange={[0, 100]}
        xPos={180} yPos={820}
        gridColor="#1E293B" gridOpacity={0.06}
        axisColor="#475569" axisWidth={2}
        xLabel="Number of Tests"
        yLabel="Required Prompt Precision"
        drawDuration={30} />
    </Sequence>

    {/* Inverse curve */}
    <Sequence from={40}>
      <AnimatedCurve
        data={[
          { x: 0, y: 95 }, { x: 5, y: 80 }, { x: 10, y: 55 },
          { x: 20, y: 35 }, { x: 30, y: 22 }, { x: 40, y: 15 },
          { x: 50, y: 10 }
        ]}
        color="#E2E8F0" width={3} opacity={0.8}
        glowRadius={8} glowOpacity={0.08}
        drawDuration={80} />
    </Sequence>

    {/* Shaded regions */}
    <Sequence from={120}>
      <ShadedRegion position="above-curve" xRange={[0, 15]}
        color="#EF4444" opacity={0.03}
        label="Over-specified" labelColor="#EF4444"
        fadeDuration={30} />
      <ShadedRegion position="below-curve" xRange={[30, 50]}
        color="#22C55E" opacity={0.03}
        label="Tests handle constraints" labelColor="#22C55E"
        fadeDuration={30} />
    </Sequence>

    {/* Left callout — dense prompt */}
    <Sequence from={160}>
      <PromptCallout
        anchorPoint={chartToScreen(5, 80)}
        calloutPos={[380, 180]} size={[280, 200]}
        fileName="parser_v1.prompt"
        fileColor="#D9944A" lineCount={50}
        badgeColor="#EF4444"
        glowColor="#EF4444" glowOpacity={0.06}
        label="5 tests → 50-line prompt"
        labelColor="#D9944A"
        promptLines={densePromptLines} />
    </Sequence>

    {/* Slider dot */}
    <Sequence from={220}>
      <CurveSlider data={curveData}
        dotSize={10} color="#E2E8F0"
        glowRadius={20} glowOpacity={0.2}
        travelDuration={120} />
    </Sequence>

    {/* Right callout — minimal prompt + tests */}
    <Sequence from={300}>
      <PromptCallout
        anchorPoint={chartToScreen(47, 12)}
        calloutPos={[1350, 500]} size={[280, 180]}
        fileName="parser_v2.prompt"
        fileColor="#22C55E" lineCount={10}
        badgeColor="#22C55E"
        glowColor="#22C55E" glowOpacity={0.06}
        label="47 tests → 10-line prompt"
        labelColor="#22C55E"
        promptLines={minimalPromptLines}
        terminal={{ command: "pdd test parser", result: "47/47 passing ✓" }} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "precision_tradeoff_curve",
  "xAxis": { "label": "Number of Tests", "range": [0, 50], "unit": "tests" },
  "yAxis": { "label": "Required Prompt Precision", "range": [0, 100], "unit": "relative" },
  "series": [
    {
      "name": "Precision-Tests Tradeoff",
      "color": "#E2E8F0",
      "curveType": "inverse_hyperbola",
      "dataPoints": [
        { "x": 0, "y": 95 },
        { "x": 5, "y": 80 },
        { "x": 10, "y": 55 },
        { "x": 20, "y": 35 },
        { "x": 30, "y": 22 },
        { "x": 40, "y": 15 },
        { "x": 50, "y": 10 }
      ]
    }
  ],
  "callouts": [
    {
      "position": "left",
      "testCount": 5,
      "promptLines": 50,
      "fileName": "parser_v1.prompt",
      "color": "#D9944A",
      "description": "Few tests — prompt must specify everything"
    },
    {
      "position": "right",
      "testCount": 47,
      "promptLines": 10,
      "fileName": "parser_v2.prompt",
      "color": "#22C55E",
      "description": "Many tests — prompt only specifies intent"
    }
  ],
  "shadedRegions": [
    { "zone": "danger", "xRange": [0, 15], "color": "#EF4444", "label": "Over-specified" },
    { "zone": "sweet_spot", "xRange": [30, 50], "color": "#22C55E", "label": "Tests handle constraints" }
  ],
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part4_005"]
}
```

---
