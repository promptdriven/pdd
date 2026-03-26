[Remotion]

# Section 4.3: Precision Tradeoff Curve — Tests vs Prompt Precision

**Tool:** Remotion
**Duration:** ~17s (510 frames @ 30fps)
**Timestamp:** 0:30 - 0:47

## Visual Description

An animated graph that reveals the core insight of the section: an inverse relationship between the number of tests and the required prompt precision.

The graph appears cleanly. X-axis: "Number of Tests" (0 to 100). Y-axis: "Required Prompt Precision" (0% to 100%). An inverse curve draws from top-left to bottom-right — a steep descent that flattens into a long tail.

A glowing dot animates along the curve. At the LEFT (few tests), the dot is high — the prompt must be extremely detailed. A callout appears: "Few tests → detailed prompt required." A mini prompt document icon appears, dense with text lines.

The dot then slides RIGHT along the curve (many tests). As it descends, the callout changes: "Many tests → minimal prompt sufficient." A mini prompt document shrinks to just a few lines, while test icons multiply around it.

The key visual: the area ABOVE the curve represents "work the prompt must do" and the area BELOW represents "work the tests handle." As the dot moves right, the prompt's burden visually shrinks.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: `#1E293B` at 0.05, 60px spacing

### Chart/Visual Elements

#### Axes
- X-axis: from (200, 850) to (1720, 850), `#475569` 2px
  - Label: "Number of Tests" — Inter, 14px, `#94A3B8`, centered below at y: 900
  - Tick marks at 0, 20, 40, 60, 80, 100 — `#475569` 1px, 8px tall
  - Tick labels: Inter, 11px, `#64748B`
- Y-axis: from (200, 850) to (200, 150), `#475569` 2px
  - Label: "Required Prompt Precision" — Inter, 14px, `#94A3B8`, rotated -90°, x: 100
  - Tick marks at 0%, 25%, 50%, 75%, 100% — `#475569` 1px, 8px wide
  - Tick labels: Inter, 11px, `#64748B`

#### Inverse Curve
- Path: exponential decay from (200, 200) to (1720, 780)
  - Data: `y = 200 + 600 * e^(-0.04 * x)` mapped to pixel space
- Stroke: `#A78BFA` (purple), 3px, solid
- Glow: `#A78BFA` at 0.15, 6px radius

#### Shaded Regions
- Above curve (prompt burden): `#F59E0B` at 0.06, fill to top
- Below curve (test coverage): `#2DD4BF` at 0.06, fill to bottom
- Region labels:
  - "Prompt does the work" — Inter, 12px, `#F59E0B` at 0.4, positioned in upper-left area
  - "Tests do the work" — Inter, 12px, `#2DD4BF` at 0.4, positioned in lower-right area

#### Animated Dot
- Circle: 8px radius, `#E2E8F0`, solid fill
- Glow: `#A78BFA` at 0.3, 12px radius
- Moves along curve from left to right

#### Callout Boxes
- Left callout (few tests): rounded rect, `#1E1E2E` bg, `#F59E0B` border at 0.3
  - "Few tests → detailed prompt" — Inter, 12px, `#F59E0B`
  - Mini prompt icon: 5 text lines (dense), `#F59E0B` at 0.4
- Right callout (many tests): rounded rect, `#1E1E2E` bg, `#2DD4BF` border at 0.3
  - "Many tests → minimal prompt" — Inter, 12px, `#2DD4BF`
  - Mini prompt icon: 2 text lines (sparse), `#2DD4BF` at 0.4
  - Surrounding test icons: 6 small check marks, `#2DD4BF` at 0.3

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in. Grid visible. Labels appear.
2. **Frame 30-90 (1-3s):** Inverse curve draws from left to right. Glow follows the drawing edge.
3. **Frame 90-150 (3-5s):** Shaded regions fill in — amber above, teal below. Region labels fade in.
4. **Frame 150-210 (5-7s):** Dot appears at top-left of curve. Left callout box appears with "Few tests → detailed prompt" and dense prompt icon.
5. **Frame 210-330 (7-11s):** Dot slides along curve toward the right. Left callout fades. The dot descends as it moves right.
6. **Frame 330-420 (11-14s):** Dot reaches lower-right region. Right callout appears: "Many tests → minimal prompt" with sparse prompt icon and test check marks.
7. **Frame 420-510 (14-17s):** Hold. The visual contrast is clear: prompt burden shrank, test coverage grew.

### Typography
- Axis labels: Inter, 14px, `#94A3B8`
- Tick labels: Inter, 11px, `#64748B`
- Region labels: Inter, 12px, respective colors at 0.4
- Callout text: Inter, 12px, respective colors

### Easing
- Axis draw: `easeOut(quad)` over 30 frames
- Curve draw: `easeInOut(cubic)` over 60 frames
- Region fill: `easeOut(quad)` over 30 frames
- Dot movement: `easeInOut(cubic)` over 120 frames
- Callout appear: `easeOut(quad)` over 20 frames
- Callout fade: `easeIn(quad)` over 15 frames

## Narration Sync
> "With few tests, your prompt must specify everything. Architecture, edge cases, error handling — all of it."
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

Segments: `part4_precision_tradeoff_005`, `part4_precision_tradeoff_006`

- **30.10s** (seg 005): Graph axes appear, curve begins drawing
- **33s**: Dot at top-left, "few tests" callout visible
- **39.80s** (seg 005 ends): Dot moving along curve
- **40.10s** (seg 006): Dot descending toward right
- **47.00s** (seg 006 ends): Dot at bottom-right, "many tests" callout visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={510}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawLine from={[200, 850]} to={[1720, 850]}
        color="#475569" width={2} drawDuration={30} />
      <DrawLine from={[200, 850]} to={[200, 150]}
        color="#475569" width={2} drawDuration={30} />
      <AxisLabels
        xLabel="Number of Tests" yLabel="Required Prompt Precision"
        xTicks={[0, 20, 40, 60, 80, 100]}
        yTicks={["0%", "25%", "50%", "75%", "100%"]}
        font="Inter" labelSize={14} tickSize={11}
        labelColor="#94A3B8" tickColor="#64748B" />
    </Sequence>

    {/* Inverse curve */}
    <Sequence from={30}>
      <AnimatedCurve
        fn={(x) => 200 + 600 * Math.exp(-0.04 * x)}
        xRange={[0, 100]} mapToPixel={[200, 1720, 850, 150]}
        color="#A78BFA" width={3}
        glowColor="#A78BFA" glowOpacity={0.15} glowRadius={6}
        drawDuration={60} />
    </Sequence>

    {/* Shaded regions */}
    <Sequence from={90}>
      <FadeIn duration={30}>
        <FillArea above curve="#A78BFA" color="#F59E0B" opacity={0.06} />
        <FillArea below curve="#A78BFA" color="#2DD4BF" opacity={0.06} />
        <Text text="Prompt does the work" font="Inter" size={12}
          color="#F59E0B" opacity={0.4} x={500} y={300} />
        <Text text="Tests do the work" font="Inter" size={12}
          color="#2DD4BF" opacity={0.4} x={1300} y={700} />
      </FadeIn>
    </Sequence>

    {/* Animated dot along curve */}
    <Sequence from={150}>
      <CurveDot
        fn={(x) => 200 + 600 * Math.exp(-0.04 * x)}
        xRange={[0, 100]} mapToPixel={[200, 1720, 850, 150]}
        radius={8} color="#E2E8F0"
        glowColor="#A78BFA" glowOpacity={0.3} glowRadius={12}
        startX={0} endX={100} duration={180}
        startFrame={0} moveFrame={60} />
    </Sequence>

    {/* Left callout — few tests */}
    <Sequence from={150}>
      <FadeIn duration={20}>
        <CalloutBox x={450} y={220}
          bg="#1E1E2E" border="#F59E0B" borderOpacity={0.3}>
          <Text text="Few tests → detailed prompt" font="Inter" size={12}
            color="#F59E0B" />
          <PromptIcon lines={5} color="#F59E0B" opacity={0.4} />
        </CalloutBox>
      </FadeIn>
    </Sequence>

    {/* Right callout — many tests */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <CalloutBox x={1350} y={600}
          bg="#1E1E2E" border="#2DD4BF" borderOpacity={0.3}>
          <Text text="Many tests → minimal prompt" font="Inter" size={12}
            color="#2DD4BF" />
          <PromptIcon lines={2} color="#2DD4BF" opacity={0.4} />
          <TestCheckmarks count={6} color="#2DD4BF" opacity={0.3} />
        </CalloutBox>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartType": "inverse_curve",
  "axes": {
    "x": { "label": "Number of Tests", "range": [0, 100], "unit": "count" },
    "y": { "label": "Required Prompt Precision", "range": [0, 100], "unit": "percent" }
  },
  "curve": {
    "function": "y = 200 + 600 * exp(-0.04 * x)",
    "color": "#A78BFA",
    "interpretation": "inverse_relationship"
  },
  "regions": [
    { "position": "above_curve", "label": "Prompt does the work", "color": "#F59E0B" },
    { "position": "below_curve", "label": "Tests do the work", "color": "#2DD4BF" }
  ],
  "callouts": [
    { "position": "left", "label": "Few tests → detailed prompt", "promptLines": 5 },
    { "position": "right", "label": "Many tests → minimal prompt", "promptLines": 2, "testCount": 6 }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_005", "part4_precision_tradeoff_006"]
}
```

---
