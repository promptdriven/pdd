[Remotion]

# Section 1.8: Crossing Lines Moment — Generation Beats Total Cost

**Tool:** Remotion
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 5:20 - 5:45

## Visual Description

Return to the triple-line chart from specs 03-04, but now with critical additions. The blue "generate" line, which had plunged through the 2023-2025 period, is shown crossing below BOTH the dashed "total cost with debt" line AND the solid "immediate patch cost" line. This is the economic crossing point for code — the equivalent of "The Threshold" from the sock chart.

The crossing happens in two beats:
1. First, the blue line crosses below the dashed line — generation becomes cheaper than patching-with-debt.
2. Then it crosses below even the solid line — generation becomes cheaper than a single patch.

A glowing label appears at the second crossing: "We are here." with a pulsing dot.

Additionally, the chart shows a **fork** in the immediate patch cost line at ~2020. The lower fork is labeled "Small codebase" and plunges down. The upper fork is labeled "Large codebase" and stays flat (~10-12 hours). An annotation: "Same tools. Different codebase sizes." This visualizes the METR finding and the trap of accumulation.

A small arrow curves from the lower fork upward toward the upper fork, labeled "Every patch adds code" — showing that patching pushes you from the good world to the bad world.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Chart area: same layout as spec 03

### Chart/Visual Elements

#### Chart Base
- Same axes and structure as spec 03 (2015-2025, Developer Hours)
- All three original lines present
- AI milestone markers present but dimmed further (0.06 opacity)

#### Forked Patch Line
- At 2020, the solid amber line forks:
  - **Lower fork** ("Small codebase"): `#5AAA6E` 2px, drops to ~1hr by 2025
  - **Upper fork** ("Large codebase"): `#E74C3C` 2px, stays flat at ~10-12hrs
- Fork labels: Inter, 11px, respective colors at 0.6
- Fork point: small circle at 2020, `#D9944A` at 0.5

#### Annotation — Same Tools, Different Sizes
- "Same tools. Different codebase sizes." — Inter, 12px, `#94A3B8` at 0.5
- Positioned between the two forks, slightly right of center
- Connecting lines: thin dashed, `#94A3B8` at 0.15, pointing to both forks

#### METR Annotation (Upper Fork)
- "METR, 2025: experienced devs 19% slower" — Inter, 9px, `#E74C3C` at 0.45
- "Developers believed +20%. Reality: −19%." — Inter, 9px, `#E74C3C` at 0.35
- Positioned near the upper fork endpoint

#### Accumulation Arrow
- Curved arrow from lower fork arcing upward to upper fork
- Color: `#D9944A` at 0.3, 2px, with arrowhead
- Label: "Every patch adds code" — Inter, 10px, `#D9944A` at 0.5, along the curve

#### Generation Line Crossing
- Blue line (`#4A90D9`) crosses below dashed amber, then below solid amber
- At the second crossing point: glowing dot, 10px, `#4A90D9` with 20px glow at 0.2
- Label: "We are here." — Inter, 16px, bold, `#4A90D9` at 0.85, with subtle glow
- Small annotation: "Small modules. Clear prompts. Always fits in context." — Inter, 9px, `#4A90D9` at 0.4

#### Terminal Breadcrumb
- `pdd generate` — JetBrains Mono, 10px, `#4A90D9` at 0.12, bottom-right (1800, 1040)

### Animation Sequence
1. **Frame 0-60 (0-2s):** Chart fades back in from developer shot. Original three lines visible. Quick re-establishment.
2. **Frame 60-180 (2-6s):** Solid amber line forks at 2020. Lower fork (green) plunges. Upper fork (red) stays flat. Fork labels appear.
3. **Frame 180-240 (6-8s):** "Same tools. Different codebase sizes." annotation fades in.
4. **Frame 240-330 (8-11s):** METR annotations appear near the upper fork. The perception gap data lands.
5. **Frame 330-390 (11-13s):** Curved accumulation arrow draws from lower to upper fork. "Every patch adds code" label appears.
6. **Frame 390-480 (13-16s):** Blue "generate" line pulses and extends. Crosses below dashed line. First crossing marked.
7. **Frame 480-540 (16-18s):** Blue line crosses below solid line. "We are here." label appears with glowing dot.
8. **Frame 540-600 (18-20s):** Small annotation about prompts appears. Terminal breadcrumb fades in.
9. **Frame 600-750 (20-25s):** Hold. The crossing point pulses. The economic argument is complete.

### Typography
- Fork labels: Inter, 11px, respective colors at 0.6
- Annotation text: Inter, 12px, `#94A3B8` at 0.5
- METR citations: Inter, 9px, `#E74C3C` at 0.35-0.45
- Arrow label: Inter, 10px, `#D9944A` at 0.5
- "We are here.": Inter, 16px, bold, `#4A90D9` at 0.85
- Prompt annotation: Inter, 9px, `#4A90D9` at 0.4
- Terminal breadcrumb: JetBrains Mono, 10px, `#4A90D9` at 0.12

### Easing
- Chart fade-in: `easeOut(quad)` over 30 frames
- Fork animation: `easeOut(cubic)` line draw over 40 frames each
- Arrow draw: `easeOut(cubic)` over 30 frames
- Crossing point glow: `easeOut(quad)` appear, `easeInOut(sine)` pulse on 50-frame cycle
- Label fades: `easeOut(quad)` over 15 frames

## Narration Sync
> "On a small codebase — a few thousand lines — patching with AI is genuinely transformative. The context window covers everything. That's real."
> "But on a large codebase — the kind you end up with after years of patching — experienced developers are actually nineteen percent slower with AI tools."
> "And that's the trap: every patch makes the codebase bigger. So patching pushes you from the world where AI helps into the world where it doesn't."
> "Regeneration doesn't have this problem. A prompt is a fifth to a tenth the size of the code it governs."
> "Meanwhile, generation just crossed below both lines. The debt doesn't just slow down — it resets."

Segments: `part1_economics_025`, `part1_economics_026`, `part1_economics_032`, `part1_economics_033`

- **5:20** ("small codebase"): Lower fork visible, green, plunging down
- **5:26** ("large codebase"): Upper fork visible, red, flat — METR data appears
- **5:32** ("that's the trap"): Accumulation arrow draws
- **5:36** ("Regeneration doesn't have this problem"): Blue line pulses
- **5:40** ("crossed below both lines"): "We are here." moment

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Chart base with original three lines */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <TripleLineChart data={chartData}
          milestoneOpacity={0.06} />
      </FadeIn>
    </Sequence>

    {/* Forked patch line */}
    <Sequence from={60}>
      <ForkedLine
        forkPoint={{ x: 2020, y: 7 }}
        lowerFork={{ data: smallCodebaseData, color: "#5AAA6E",
          label: "Small codebase" }}
        upperFork={{ data: largeCodebaseData, color: "#E74C3C",
          label: "Large codebase" }}
        drawDuration={40}
      />
    </Sequence>

    {/* Same tools annotation */}
    <Sequence from={180}>
      <FadeIn duration={15}>
        <AnnotationText
          text="Same tools. Different codebase sizes."
          font="Inter" size={12} color="#94A3B8" opacity={0.5}
          x={annotationX} y={annotationY}
        />
      </FadeIn>
    </Sequence>

    {/* METR annotations */}
    <Sequence from={240}>
      <FadeIn duration={15}>
        <AnnotationCallout
          lines={[
            "METR, 2025: experienced devs 19% slower",
            "Developers believed +20%. Reality: −19%."
          ]}
          color="#E74C3C"
          targetPoint={upperForkEnd}
        />
      </FadeIn>
    </Sequence>

    {/* Accumulation arrow */}
    <Sequence from={330}>
      <CurvedArrow
        from={lowerForkMid} to={upperForkMid}
        color="#D9944A" opacity={0.3} width={2}
        label="Every patch adds code"
        drawDuration={30}
      />
    </Sequence>

    {/* Generate line crossing */}
    <Sequence from={390}>
      <AnimatedLine
        data={generateLineCrossing} color="#4A90D9"
        strokeWidth={3} drawDuration={60}
        pulseOnComplete
      />
    </Sequence>

    {/* "We are here" label */}
    <Sequence from={480}>
      <CrossingPoint
        x={crossingX} y={crossingY}
        radius={10} glowRadius={20}
        label="We are here."
        labelFont="Inter" labelSize={16} labelWeight={700}
        labelColor="#4A90D9"
      />
    </Sequence>

    {/* Terminal breadcrumb */}
    <Sequence from={540}>
      <FadeIn duration={15}>
        <TerminalSnippet text="pdd generate"
          font="JetBrains Mono" size={10}
          color="#4A90D9" opacity={0.12}
          x={1800} y={1040} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartType": "forked_line_crossing",
  "forkedLine": {
    "forkPoint": { "x": 2020, "y": 7 },
    "lowerFork": {
      "id": "small_codebase",
      "label": "Small codebase",
      "color": "#5AAA6E",
      "data": [
        { "x": 2020, "y": 7 }, { "x": 2022, "y": 4 },
        { "x": 2024, "y": 2 }, { "x": 2025, "y": 1 }
      ]
    },
    "upperFork": {
      "id": "large_codebase",
      "label": "Large codebase",
      "color": "#E74C3C",
      "data": [
        { "x": 2020, "y": 7 }, { "x": 2022, "y": 10 },
        { "x": 2024, "y": 11 }, { "x": 2025, "y": 12 }
      ]
    }
  },
  "crossingLabel": "We are here.",
  "metrAnnotation": {
    "perceived": "+20%",
    "actual": "−19%",
    "perceptionGap": "39 points"
  },
  "accumulationArrow": {
    "label": "Every patch adds code",
    "from": "lower_fork",
    "to": "upper_fork"
  },
  "terminalBreadcrumb": "pdd generate",
  "backgroundColor": "#0D1117",
  "narrationSegments": [
    "part1_economics_025", "part1_economics_026",
    "part1_economics_032", "part1_economics_033"
  ]
}
```

---
