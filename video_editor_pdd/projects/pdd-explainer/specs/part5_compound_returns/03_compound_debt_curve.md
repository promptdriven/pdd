[Remotion]

# Section 5.3: Compound Debt Curve — Debt × (1 + Rate)^Time

**Tool:** Remotion
**Duration:** ~17s (510 frames @ 30fps)
**Timestamp:** 0:24 - 0:41

## Visual Description

The pie chart from the previous visual morphs into an exponential growth curve. The amber maintenance slice stretches and reshapes into an exponentially growing line labeled "Debt × (1 + Rate)^Time". The area under this curve fills with a warm amber gradient, conveying the crushing weight of compound debt.

A second line appears — flat and green — labeled "Regeneration cost (debt resets each cycle)". It hugs the x-axis. The contrast between the runaway exponential and the flat line is dramatic and immediate.

A large stat callout appears: "$1.52 TRILLION annually — CISQ" to quantify the scale.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal only, `#1A2540` at 0.06, every 100px

### Chart/Visual Elements

#### Axes
- X-axis: "Time" — years 0–10 (abstract)
  - Line: 1.5px, `#334155`
  - Labels: Inter, 12px, `#64748B` at 0.6
- Y-axis: "Cost" — abstract scale
  - Line: 1.5px, `#334155`
  - Labels: Inter, 12px, `#64748B` at 0.6

#### Exponential Debt Curve
- Formula: y = base × (1 + 0.25)^x (visual representation)
- Color: `#F59E0B` (amber)
- Stroke: 3px
- Fill below: linear gradient from `#F59E0B` at 0.15 (bottom) to `#F59E0B` at 0.04 (top)
- Label: "Debt × (1 + Rate)^Time" — Inter, 16px, bold (700), `#F59E0B` at 0.9
- Label position: along curve, upper right

#### Flat Regeneration Line
- Formula: y = constant (low value)
- Color: `#4ADE80` (green)
- Stroke: 2.5px, dashed (8px dash, 4px gap)
- Label: "Regeneration cost (debt resets each cycle)" — Inter, 14px, semi-bold (600), `#4ADE80` at 0.8
- Label position: right end of line

#### CISQ Stat
- "$1.52T" — Inter, 48px, bold (800), `#F59E0B` at 0.9
- "annually — CISQ" — Inter, 16px, regular (400), `#94A3B8` at 0.6
- Position: upper-left area, (200, 180)
- Background: `#1A2540` at 0.4, rounded 12px, padding 20px

### Animation Sequence
1. **Frame 0-60 (0-2s):** Pie chart morphs: the amber slice stretches rightward, reshaping into the exponential curve. The green slice compresses into the flat line. Axes fade in.
2. **Frame 60-150 (2-5s):** Exponential curve draws rightward with accelerating steepness. Area fill follows. The growth feels relentless.
3. **Frame 150-210 (5-7s):** "Debt × (1 + Rate)^Time" label fades in along the curve.
4. **Frame 210-270 (7-9s):** Flat green dashed line draws from left to right. Label appears.
5. **Frame 270-360 (9-12s):** CISQ stat fades in with scale-up. "$1.52T" is large and impactful.
6. **Frame 360-450 (12-15s):** Hold. The exponential continues to creep slightly upward (subtle animation).
7. **Frame 450-510 (15-17s):** Transition — chart elements begin repositioning for the next visual.

### Typography
- Curve label: Inter, 16px, bold (700), `#F59E0B`
- Flat line label: Inter, 14px, semi-bold (600), `#4ADE80`
- CISQ value: Inter, 48px, bold (800), `#F59E0B`
- CISQ source: Inter, 16px, regular (400), `#94A3B8`
- Axis labels: Inter, 12px, regular (400), `#64748B`

### Easing
- Morph transition: `easeInOut(cubic)` over 60 frames
- Curve draw: `easeIn(quad)` over 90 frames (accelerating steepness)
- Label fade: `easeOut(quad)` over 20 frames
- Flat line draw: `easeOut(quad)` over 40 frames
- CISQ scale-up: `easeOut(back)` over 25 frames

## Narration Sync
> "And those costs compound — literally. Technical debt follows a compound interest curve. CISQ puts the US total at one-point-five-two trillion dollars annually. That's not a metaphor. It's the math of accumulation."

Segment: `part5_compound_returns_003`

- **0:24** ("costs compound — literally"): Pie chart begins morphing into exponential curve
- **0:28** ("compound interest curve"): Curve draws with accelerating steepness
- **0:32** ("CISQ puts"): $1.52T stat appears
- **0:36** ("not a metaphor"): Green flat line draws for contrast
- **0:41** ("math of accumulation"): Hold on complete chart

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={510}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <HorizontalGrid spacing={100} color="#1A2540" opacity={0.06} />

    {/* Morph from pie chart */}
    <Sequence from={0} durationInFrames={60}>
      <MorphTransition
        from="pie_chart" to="exponential_curve"
        duration={60} easing="easeInOutCubic" />
    </Sequence>

    {/* Axes */}
    <Sequence from={30}>
      <FadeIn duration={30}>
        <Axes xLabel="Time" yLabel="Cost"
          color="#334155" labelColor="#64748B" />
      </FadeIn>
    </Sequence>

    {/* Exponential curve */}
    <Sequence from={60}>
      <DrawLine
        path={exponentialPath} color="#F59E0B"
        strokeWidth={3} duration={90}
        fillBelow={{ gradient: ['#F59E0B26', '#F59E0B0A'] }} />
    </Sequence>

    {/* Curve label */}
    <Sequence from={150}>
      <FadeIn duration={20}>
        <Text text="Debt × (1 + Rate)^Time"
          font="Inter" size={16} weight={700}
          color="#F59E0B" opacity={0.9}
          x={1400} y={200} />
      </FadeIn>
    </Sequence>

    {/* Flat regeneration line */}
    <Sequence from={210}>
      <DrawLine
        path={flatPath} color="#4ADE80"
        strokeWidth={2.5} dashed={[8, 4]} duration={40} />
      <FadeIn duration={20}>
        <Text text="Regeneration cost (debt resets each cycle)"
          font="Inter" size={14} weight={600}
          color="#4ADE80" opacity={0.8}
          x={1300} y={720} />
      </FadeIn>
    </Sequence>

    {/* CISQ stat */}
    <Sequence from={270}>
      <ScaleIn from={0.8} to={1.0} duration={25}>
        <FadeIn duration={25}>
          <StatCard x={200} y={180}
            bg="#1A2540" bgOpacity={0.4} radius={12}>
            <Text text="$1.52T" font="Inter" size={48}
              weight={800} color="#F59E0B" />
            <Text text="annually — CISQ" font="Inter" size={16}
              weight={400} color="#94A3B8" />
          </StatCard>
        </FadeIn>
      </ScaleIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "compound_debt_curve",
  "morphFrom": "maintenance_cost_pie",
  "curves": [
    {
      "id": "debt_exponential",
      "formula": "base * (1 + 0.25)^x",
      "color": "#F59E0B",
      "strokeWidth": 3,
      "label": "Debt × (1 + Rate)^Time",
      "fill": true
    },
    {
      "id": "regeneration_flat",
      "formula": "constant",
      "color": "#4ADE80",
      "strokeWidth": 2.5,
      "dashed": true,
      "label": "Regeneration cost (debt resets each cycle)"
    }
  ],
  "stats": [
    { "value": "$1.52T", "label": "annually", "source": "CISQ", "color": "#F59E0B" }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part5_compound_returns_003"]
}
```

---
