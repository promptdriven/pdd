[Remotion]

# Section 5.4: Diverging Cost Curves — Patching vs. PDD Over Time

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 0:44 - 1:06

## Visual Description

Two diverging cost curves that make the central economic argument undeniable:

1. **"Patching" (amber, `#D9944A`):** Grows exponentially upward. Each patch adds debt, debt generates more debt. The curve accelerates relentlessly — cost compounding against you.

2. **"PDD" (green, `#5AAA6E`):** Stays flat. Each regeneration cycle resets debt to zero. Small sawtooth waves along the line show individual regeneration costs, but they never accumulate — the baseline stays level.

The gap between the curves widens dramatically over time. By the right edge of the chart, the amber curve is near the top while green hugs the bottom. A shaded region between them — labeled "The Gap" — pulses to emphasize the compounding difference.

Below the chart, two text annotations appear sequentially: "Patching accrues compound costs" (amber) and "Tests accrue compound returns" (green). The green text is the section's thesis statement.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal at 150px intervals, `#1E293B` at 0.08

### Chart/Visual Elements

#### Axes
- X-axis: "Time (years)", labeled 0-10, `#94A3B8` at 0.6, Inter 14px
- Y-axis: "Cumulative Cost", `#94A3B8` at 0.6, Inter 14px
- Axis lines: `#334155`, 1.5px

#### Patching Curve (amber exponential)
- Color: `#D9944A`, 3px solid
- Shape: Exponential growth — starts at y:75%, accelerates to y:8% by year 10
- Label: "Patching" — Inter, 16px, semi-bold (600), `#D9944A`, positioned at curve end

#### PDD Curve (green flat with sawtooth)
- Color: `#5AAA6E`, 3px solid
- Shape: Flat baseline at y:78% with small sawtooth ripples (amplitude 3%, period matching regeneration cycles)
- Label: "PDD" — Inter, 16px, semi-bold (600), `#5AAA6E`, positioned at curve end

#### Gap Region
- Shaded area between curves: linear gradient `#D9944A` at 0.06 (top) to `#5AAA6E` at 0.04 (bottom)
- "The Gap" label: Inter, 14px, `#E2E8F0` at 0.5, centered in the shaded region

#### Thesis Annotations (below chart)
- "Patching accrues compound costs." — Inter, 18px, semi-bold (600), `#D9944A`, y: 850
- "Tests accrue compound returns." — Inter, 18px, semi-bold (600), `#5AAA6E`, y: 890

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes from previous chart relabel. Grid stabilizes.
2. **Frame 30-180 (1-6s):** Both curves draw simultaneously from left to right. Amber curve begins accelerating upward. Green stays flat with sawtooth ripples.
3. **Frame 180-300 (6-10s):** Curves continue diverging. The gap widens dramatically. Shaded gap region fills between them.
4. **Frame 300-360 (10-12s):** "The Gap" label fades in. Gap pulses subtly.
5. **Frame 360-420 (12-14s):** "Patching accrues compound costs." fades in below chart.
6. **Frame 420-480 (14-16s):** "Tests accrue compound returns." fades in below — the thesis statement.
7. **Frame 480-600 (16-20s):** Hold. The contrast between the curves speaks.
8. **Frame 600-660 (20-22s):** Chart fades slightly, preparing for investment table overlay.

### Typography
- Axis labels: Inter, 14px, regular (400), `#94A3B8` at 0.6
- Curve labels: Inter, 16px, semi-bold (600), respective colors
- Gap label: Inter, 14px, regular (400), `#E2E8F0` at 0.5
- Thesis statements: Inter, 18px, semi-bold (600), respective colors

### Easing
- Amber curve draw: `easeIn(quad)` — accelerating upward
- Green curve draw: `easeOut(quad)` — smooth, steady
- Gap fill: `easeOut(quad)` over 60 frames
- Gap pulse: `easeInOut(sine)` on 60-frame cycle, opacity 0.04-0.08
- Thesis fade-in: `easeOut(quad)` over 25 frames
- Chart fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Patching accrues compound costs. Each patch adds debt. Debt generates more debt."
> "But the mold works the other way. Each test you write constrains every future generation. Today's. Next month's. Next year's. Tests accrue compound returns."

Segments: `part5_compound_returns_003`

- **43.84s** (seg 003): Curves begin drawing — "Patching accrues compound costs"
- **48.00s**: Divergence accelerating — "Each patch adds debt. Debt generates more debt."
- **52.00s**: Green line visible — "But the mold works the other way"
- **58.00s**: Thesis annotations — "Tests accrue compound returns"
- **65.66s** (seg 003 ends): Hold on diverging curves

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <HorizontalGrid spacing={150} color="#1E293B" opacity={0.08} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        xRange={[0, 10]} xLabel="Time (years)"
        yLabel="Cumulative Cost"
        color="#334155" labelColor="#94A3B8"
      />
    </Sequence>

    {/* Both curves drawing */}
    <Sequence from={30}>
      <AnimatedLine
        data={patchingExponentialData}
        color="#D9944A" strokeWidth={3}
        drawDuration={270} easing="easeInQuad"
      />
      <AnimatedLine
        data={pddFlatSawtoothData}
        color="#5AAA6E" strokeWidth={3}
        drawDuration={270} easing="easeOutQuad"
      />
    </Sequence>

    {/* Gap shaded region */}
    <Sequence from={180}>
      <ShadedArea
        upperBound={patchingExponentialData}
        lowerBound={pddFlatSawtoothData}
        gradient={{ top: "#D9944A", topOpacity: 0.06,
                    bottom: "#5AAA6E", bottomOpacity: 0.04 }}
        fillDuration={60}
      />
    </Sequence>

    {/* Gap label */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Text text="The Gap" font="Inter" size={14}
          color="#E2E8F0" opacity={0.5}
          x={1100} y={450} align="center" />
      </FadeIn>
    </Sequence>

    {/* Curve end labels */}
    <Sequence from={270}>
      <FadeIn duration={20}>
        <Text text="Patching" font="Inter" size={16}
          weight={600} color="#D9944A" x={1350} y={100} />
        <Text text="PDD" font="Inter" size={16}
          weight={600} color="#5AAA6E" x={1350} y={750} />
      </FadeIn>
    </Sequence>

    {/* Thesis annotations */}
    <Sequence from={360}>
      <FadeIn duration={25}>
        <Text text="Patching accrues compound costs."
          font="Inter" size={18} weight={600}
          color="#D9944A" x={960} y={850} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={420}>
      <FadeIn duration={25}>
        <Text text="Tests accrue compound returns."
          font="Inter" size={18} weight={600}
          color="#5AAA6E" x={960} y={890} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade transition */}
    <Sequence from={600}>
      <FadeOut duration={60} targetOpacity={0.3} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "diverging_curves",
  "chartId": "patching_vs_pdd_compounding",
  "xAxis": { "label": "Time (years)", "range": [0, 10] },
  "yAxis": { "label": "Cumulative Cost" },
  "series": [
    {
      "id": "patching_exponential",
      "label": "Patching",
      "color": "#D9944A",
      "type": "exponential",
      "data": [
        { "x": 0, "y": 0.10 }, { "x": 1, "y": 0.13 },
        { "x": 2, "y": 0.17 }, { "x": 3, "y": 0.23 },
        { "x": 4, "y": 0.31 }, { "x": 5, "y": 0.42 },
        { "x": 6, "y": 0.55 }, { "x": 7, "y": 0.68 },
        { "x": 8, "y": 0.80 }, { "x": 9, "y": 0.88 },
        { "x": 10, "y": 0.95 }
      ]
    },
    {
      "id": "pdd_flat",
      "label": "PDD",
      "color": "#5AAA6E",
      "type": "flat_sawtooth",
      "baseline": 0.10,
      "sawtoothAmplitude": 0.03,
      "data": [
        { "x": 0, "y": 0.10 }, { "x": 1, "y": 0.10 },
        { "x": 2, "y": 0.10 }, { "x": 3, "y": 0.10 },
        { "x": 4, "y": 0.10 }, { "x": 5, "y": 0.10 },
        { "x": 6, "y": 0.10 }, { "x": 7, "y": 0.10 },
        { "x": 8, "y": 0.10 }, { "x": 9, "y": 0.10 },
        { "x": 10, "y": 0.10 }
      ]
    }
  ],
  "gap": {
    "label": "The Gap",
    "gradient": { "top": "#D9944A", "bottom": "#5AAA6E" }
  },
  "thesisStatements": [
    { "text": "Patching accrues compound costs.", "color": "#D9944A" },
    { "text": "Tests accrue compound returns.", "color": "#5AAA6E" }
  ],
  "narrationSegments": ["part5_compound_returns_003"]
}
```

---
