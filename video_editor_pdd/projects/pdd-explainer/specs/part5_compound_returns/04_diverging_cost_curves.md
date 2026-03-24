[Remotion]

# Section 5.4: Diverging Cost Curves — Patching vs PDD

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 0:42 - 1:02

## Visual Description

Two dramatically diverging curves dominate the screen. The amber "Patching" curve grows exponentially upward — each patch adds debt, debt generates more debt. The green "PDD" curve stays flat near the bottom — cost resets each regeneration cycle.

The gap between them widens over time, becoming a massive visual gulf. Faint annotations appear at intervals: on the patching side, small "+debt" labels accumulate; on the PDD side, small "+test" labels accumulate. The message is clear: one compounds against you, the other compounds for you.

A key transition happens mid-visual: the narration pivots from costs to returns. At that moment, the green PDD line develops small upward tick marks representing accumulated tests — each test constrains future generations. These ticks stack, showing compound returns growing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal, `#1A2540` at 0.06, every 120px

### Chart/Visual Elements

#### Axes
- X-axis: "Time" — abstract marks: "Now", "6 months", "1 year", "2 years", "5 years"
  - Line: 1.5px, `#334155`
  - Labels: Inter, 12px, `#64748B` at 0.6
- Y-axis: "Cost / Value" — abstract scale
  - Line: 1.5px, `#334155`

#### Patching Curve (Exponential Up)
- Color: `#F59E0B` (amber)
- Stroke: 3px
- Fill below: `#F59E0B` at 0.08
- Grows exponentially — visually dramatic steepening
- Label: "Patching" — Inter, 18px, bold (700), `#F59E0B`
- Small "+debt" annotations: Inter, 10px, `#F59E0B` at 0.4, scattered along curve

#### PDD Curve (Flat with Return Ticks)
- Color: `#4ADE80` (green)
- Stroke: 3px
- Stays near baseline — flat cost
- Label: "PDD" — Inter, 18px, bold (700), `#4ADE80`
- After pivot: small upward tick marks along line, each labeled "+test"
  - Ticks: 2px wide, 12-20px tall, `#4ADE80` at 0.6
  - Each tick represents a test constraining future generations
  - Ticks accumulate and grow slightly taller over time

#### Gap Visualization
- The space between curves fills with a subtle gradient
- Color: `#F59E0B` at 0.03 (faint amber wash showing the growing cost)
- At 5-year mark: gap is enormous

#### Narration Pivot Marker
- At approximately frame 300 (10s), a thin vertical dashed line
- Label: "Tests accrue compound returns" — Inter, 14px, italic, `#4ADE80` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes visible. Both curves start from origin at same point.
2. **Frame 30-120 (1-4s):** Both curves begin drawing rightward. Patching starts curving upward. PDD stays flat. "+debt" labels appear on patching curve.
3. **Frame 120-210 (4-7s):** Gap widens dramatically. Patching curve steepens. More "+debt" labels.
4. **Frame 210-270 (7-9s):** Narration pivots. "PDD" label emphasizes. Vertical dashed pivot line appears.
5. **Frame 270-390 (9-13s):** "+test" tick marks begin appearing along PDD line. Each tick pops in with a small bounce. Ticks accumulate, growing slightly taller.
6. **Frame 390-480 (13-16s):** "Tests accrue compound returns" annotation fades in. Gap between curves is at maximum.
7. **Frame 480-540 (16-18s):** Hold on final state. The contrast is complete.
8. **Frame 540-600 (18-20s):** Gentle fade transition to next visual.

### Typography
- Curve labels: Inter, 18px, bold (700)
- "+debt" / "+test" annotations: Inter, 10px, regular (400), at 0.4
- Pivot annotation: Inter, 14px, italic, `#4ADE80` at 0.7
- Axis labels: Inter, 12px, regular (400), `#64748B`

### Easing
- Curve draw: `easeIn(quad)` for patching (accelerating), `linear` for PDD (steady)
- "+debt" appear: `easeOut(quad)` over 10 frames each
- "+test" ticks: `easeOut(back)` over 12 frames each (small bounce)
- Pivot line: `easeOut(quad)` over 20 frames
- Gap fill: `linear` opacity increase

## Narration Sync
> "Patching accrues compound costs. Each patch adds debt. Debt generates more debt. But the mold works the other way. Each test you write constrains every future generation. Today's. Next month's. Next year's. Tests accrue compound returns."

Segments: `part5_compound_returns_004`, `part5_compound_returns_005`

- **0:42** ("Patching accrues compound costs"): Both curves begin drawing, patching curves upward
- **0:45** ("Each patch adds debt"): "+debt" labels appear on patching curve
- **0:49** ("the mold works the other way"): Pivot — focus shifts to PDD line
- **0:53** ("Each test you write constrains"): "+test" ticks begin appearing on PDD line
- **0:57** ("Today's. Next month's. Next year's."): Ticks accumulate rapidly
- **1:00** ("compound returns"): Full chart visible, gap at maximum

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <HorizontalGrid spacing={120} color="#1A2540" opacity={0.06} />
    <Axes xLabels={["Now", "6 months", "1 year", "2 years", "5 years"]}
      yLabel="Cost / Value" color="#334155" />

    {/* Patching curve — exponential */}
    <Sequence from={30}>
      <AnimatedCurve
        path={patchingExponential}
        color="#F59E0B" strokeWidth={3}
        fillBelow="#F59E0B0A"
        drawDuration={450} easing="easeInQuad" />
      <CurveLabel text="Patching" color="#F59E0B"
        font="Inter" size={18} weight={700} />
    </Sequence>

    {/* +debt annotations */}
    <Sequence from={90}>
      <StaggeredAnnotations
        texts={["+debt", "+debt", "+debt", "+debt", "+debt"]}
        positions={debtPositions}
        color="#F59E0B" opacity={0.4}
        staggerDelay={30} />
    </Sequence>

    {/* PDD curve — flat */}
    <Sequence from={30}>
      <AnimatedCurve
        path={pddFlat}
        color="#4ADE80" strokeWidth={3}
        drawDuration={450} easing="linear" />
      <CurveLabel text="PDD" color="#4ADE80"
        font="Inter" size={18} weight={700} />
    </Sequence>

    {/* Gap fill */}
    <Sequence from={120}>
      <GapFill upper={patchingExponential} lower={pddFlat}
        color="#F59E0B" opacity={0.03} />
    </Sequence>

    {/* Pivot marker */}
    <Sequence from={210}>
      <FadeIn duration={20}>
        <DashedLine vertical x={pivotX}
          color="#4ADE80" opacity={0.3} />
      </FadeIn>
    </Sequence>

    {/* +test ticks */}
    <Sequence from={270}>
      <StaggeredTicks
        positions={testTickPositions}
        color="#4ADE80" opacity={0.6}
        heights={[12, 14, 15, 16, 17, 18, 19, 20]}
        staggerDelay={15} easing="easeOutBack" />
    </Sequence>

    {/* Compound returns annotation */}
    <Sequence from={390}>
      <FadeIn duration={20}>
        <Text text="Tests accrue compound returns"
          font="Inter" size={14} weight={400}
          style="italic" color="#4ADE80" opacity={0.7}
          x={pivotX + 20} y={600} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "diverging_cost_curves",
  "curves": [
    {
      "id": "patching_exponential",
      "label": "Patching",
      "color": "#F59E0B",
      "type": "exponential",
      "direction": "up",
      "annotations": ["+debt", "+debt", "+debt", "+debt", "+debt"]
    },
    {
      "id": "pdd_flat",
      "label": "PDD",
      "color": "#4ADE80",
      "type": "flat",
      "annotations": ["+test", "+test", "+test", "+test", "+test", "+test", "+test", "+test"]
    }
  ],
  "xAxis": ["Now", "6 months", "1 year", "2 years", "5 years"],
  "pivotLabel": "Tests accrue compound returns",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part5_compound_returns_004", "part5_compound_returns_005"]
}
```

---
