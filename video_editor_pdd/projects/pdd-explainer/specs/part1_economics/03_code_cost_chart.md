[Remotion]

# Section 1.3: Code Cost Chart — Generate vs Patch vs Total Debt

**Tool:** Remotion
**Duration:** ~42s (1260 frames @ 30fps)
**Timestamp:** 0:43 - 1:25

## Visual Description

A complex animated chart that is the centerpiece of Part 1. Similar structure to the sock chart but for code. The Y-axis is "Cost (Developer Hours)". The X-axis spans ~2010-2025+.

Three elements animate onto the chart in sequence:

1. **Blue line ("Cost to generate"):** Starts high (~20 dev-hours), stays flat through 2021 (Codex barely dips it), then plunges steeply starting 2023 (GPT-4, Claude, Gemini).
2. **Amber solid line ("Immediate patch cost"):** Starts low (~2 hours), holds relatively flat, then starts dropping post-2020 as Copilot and AI coding tools help with individual fixes.
3. **Amber dashed line ("Total cost with debt"):** Sits at the TOP of the chart (~18-20 hours). Barely moves despite the solid line dropping. A shaded area between the solid and dashed amber lines represents accumulated technical debt — and it EXPANDS as the solid line drops.

Key dates appear on the blue line as it falls: Codex (2021), GPT-4 (2023), Claude (2023), Gemini (2024). The visual drama: the blue generation line is in freefall while the dashed total-cost line barely budges. The viewer's lived experience (patches getting easier) is validated by the solid line — but the bigger picture (total cost unchanged) is revealed by the dashed line.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: horizontal dashed at `#1E293B` at 0.1

### Chart/Visual Elements

#### Axes
- X-axis: 2010 to 2026, tick marks every 2 years, labels at bottom
  - Color: `#475569` at 0.6, Inter 12px
- Y-axis: "Cost (Developer Hours)" — 0 to 25
  - Color: `#475569` at 0.6, Inter 12px
- Axis lines: `#334155` at 0.3, 1px

#### Lines
- **Generate (blue):** `#4A90D9`, 3px solid stroke
  - Data: (2010, 20), (2015, 19), (2020, 18), (2021, 17), (2022, 16), (2023, 8), (2024, 3), (2025, 1.5)
  - Label: "Cost to generate" — Inter, 13px, `#4A90D9`

- **Immediate patch (amber solid):** `#D9944A`, 3px solid stroke
  - Data: (2010, 3), (2015, 2.8), (2020, 2.5), (2021, 2.0), (2022, 1.5), (2023, 1.2), (2024, 0.8), (2025, 0.6)
  - Label: "Immediate patch cost" — Inter, 13px, `#D9944A`

- **Total cost with debt (amber dashed):** `#D9944A`, 2px dashed stroke, dash pattern 8,6
  - Data: (2010, 18), (2015, 18.5), (2020, 19), (2021, 19), (2022, 19.5), (2023, 20), (2024, 20.5), (2025, 21)
  - Label: "Total cost (with debt)" — Inter, 13px, `#D9944A` at 0.6

#### Debt Shaded Area
- Between solid amber and dashed amber lines
- Fill: `#D9944A` at 0.08, gradient darker toward the dashed line
- Animates to expand as the solid line drops

#### AI Milestone Labels
- "Codex" at (2021, 17): Inter, 11px, `#4A90D9` at 0.5, with connecting dot
- "GPT-4" at (2023, 8): Inter, 11px, `#4A90D9` at 0.7, with connecting dot
- "Claude" at (2023.3, 7): Inter, 11px, `#4A90D9` at 0.7, offset below GPT-4
- "Gemini" at (2024, 3): Inter, 11px, `#4A90D9` at 0.6, with connecting dot

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in. Grid lines appear. Title: "Cost (Developer Hours)".
2. **Frame 30-120 (1-4s):** Blue "generate" line draws from 2010. Flat and high.
3. **Frame 120-240 (4-8s):** Amber solid "immediate patch" line draws. Low and flat. Amber dashed "total cost" line draws at top.
4. **Frame 240-360 (8-12s):** Debt shaded area fills between the two amber lines.
5. **Frame 360-420 (12-14s):** AI milestone labels appear on blue line. Codex barely dips.
6. **Frame 420-600 (14-20s):** Blue line PLUNGES from 2023 onward. GPT-4, Claude labels appear as line falls.
7. **Frame 600-720 (20-24s):** Solid amber line drops post-2020. The viewer's lived experience validated.
8. **Frame 720-900 (24-30s):** Camera pulls back. Debt area EXPANDS upward as solid line drops. Dashed line barely moves.
9. **Frame 900-1260 (30-42s):** Hold. The gap between solid and dashed is enormous. The disconnect is visible.

### Typography
- Chart title: Inter, 20px, bold (700), `#E2E8F0`, top-left
- Axis labels: Inter, 12px, `#475569` at 0.6
- Line labels: Inter, 13px, respective colors
- Milestone labels: Inter, 11px, `#4A90D9` at varying opacities

### Easing
- Line draw: `easeInOut(cubic)` for steady portions, `easeIn(quad)` for the plunge
- Blue line plunge (2023+): accelerating `easeIn(cubic)` — feels like freefall
- Debt area expansion: `easeOut(quad)` — ominous slow reveal
- Milestone labels: `easeOut(quad)` over 15 frames each
- Dashed line steadiness: `linear` — emphasizing how little it moves

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. You needed a developer — a human brain, months of context-building, domain expertise. Patching was always cheaper."
> "something else happened. AI made each individual patch faster and faster. You can feel this. Every developer I talk to says the same thing: 'I'm shipping patches faster than ever.' They're right."
> "Each patch is getting faster. You can feel it. Your tools are better."
> "But watch the dashed line. The total cost — including the debt each patch leaves behind."
> "even though each patch is cheaper, you're doing more of them, and each one deposits a thin layer of complexity that the next patch has to navigate."

Segments: `part1_economics_008` through `part1_economics_013`

- **43.52s** ("Now look at code"): Chart axes appear, transition from sock chart
- **45.74s** ("For decades, generating new code"): Blue line begins drawing, high and flat
- **59.88s** ("AI made each individual patch faster"): Solid amber line begins dropping
- **75.78s** ("Each patch is getting faster"): Focus on dropping solid line
- **81.78s** ("But watch the dashed line"): Dashed line highlighted, debt area pulses
- **86.96s** ("even though each patch is cheaper"): Debt area expanding, gap visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1260}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Axes */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <ChartAxes
          xRange={[2010, 2026]} yRange={[0, 25]}
          xLabel="Year" yLabel="Cost (Developer Hours)"
          gridColor="#1E293B" gridOpacity={0.1}
          axisColor="#334155" labelColor="#475569" />
      </FadeIn>
    </Sequence>

    {/* Blue generate line */}
    <Sequence from={30}>
      <AnimatedLine
        data={[
          [2010, 20], [2015, 19], [2020, 18], [2021, 17],
          [2022, 16], [2023, 8], [2024, 3], [2025, 1.5]
        ]}
        color="#4A90D9" strokeWidth={3}
        drawDuration={540} label="Cost to generate" />
    </Sequence>

    {/* Amber solid (immediate patch) */}
    <Sequence from={120}>
      <AnimatedLine
        data={[
          [2010, 3], [2015, 2.8], [2020, 2.5], [2021, 2.0],
          [2022, 1.5], [2023, 1.2], [2024, 0.8], [2025, 0.6]
        ]}
        color="#D9944A" strokeWidth={3} style="solid"
        drawDuration={480} label="Immediate patch cost" />
    </Sequence>

    {/* Amber dashed (total cost with debt) */}
    <Sequence from={120}>
      <AnimatedLine
        data={[
          [2010, 18], [2015, 18.5], [2020, 19], [2021, 19],
          [2022, 19.5], [2023, 20], [2024, 20.5], [2025, 21]
        ]}
        color="#D9944A" strokeWidth={2} style="dashed"
        dashPattern={[8, 6]} drawDuration={480}
        label="Total cost (with debt)" labelOpacity={0.6} />
    </Sequence>

    {/* Debt shaded area */}
    <Sequence from={240}>
      <FillArea
        upperLine="total_cost_debt" lowerLine="immediate_patch"
        fillColor="#D9944A" opacity={0.08}
        fillDuration={300} />
    </Sequence>

    {/* AI milestone labels on blue line */}
    <Sequence from={360}>
      <MilestoneLabel text="Codex" x={2021} y={17} color="#4A90D9" opacity={0.5} />
    </Sequence>
    <Sequence from={420}>
      <MilestoneLabel text="GPT-4" x={2023} y={8} color="#4A90D9" opacity={0.7} />
      <MilestoneLabel text="Claude" x={2023} y={6} color="#4A90D9" opacity={0.7} offset={20} />
    </Sequence>
    <Sequence from={480}>
      <MilestoneLabel text="Gemini" x={2024} y={3} color="#4A90D9" opacity={0.6} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_multi_line_chart",
  "xAxis": { "label": "Year", "range": [2010, 2026], "ticks": "2y" },
  "yAxis": { "label": "Cost (Developer Hours)", "range": [0, 25] },
  "series": [
    {
      "id": "generate_cost",
      "label": "Cost to generate",
      "color": "#4A90D9",
      "strokeWidth": 3,
      "style": "solid",
      "data": [[2010, 20], [2015, 19], [2020, 18], [2021, 17], [2022, 16], [2023, 8], [2024, 3], [2025, 1.5]]
    },
    {
      "id": "immediate_patch",
      "label": "Immediate patch cost",
      "color": "#D9944A",
      "strokeWidth": 3,
      "style": "solid",
      "data": [[2010, 3], [2015, 2.8], [2020, 2.5], [2021, 2.0], [2022, 1.5], [2023, 1.2], [2024, 0.8], [2025, 0.6]]
    },
    {
      "id": "total_cost_debt",
      "label": "Total cost (with debt)",
      "color": "#D9944A",
      "strokeWidth": 2,
      "style": "dashed",
      "data": [[2010, 18], [2015, 18.5], [2020, 19], [2021, 19], [2022, 19.5], [2023, 20], [2024, 20.5], [2025, 21]]
    }
  ],
  "milestones": [
    { "label": "Codex", "year": 2021 },
    { "label": "GPT-4", "year": 2023 },
    { "label": "Claude", "year": 2023 },
    { "label": "Gemini", "year": 2024 }
  ],
  "debtArea": {
    "upper": "total_cost_debt",
    "lower": "immediate_patch",
    "color": "#D9944A",
    "opacity": 0.08
  },
  "narrationSegments": ["part1_economics_008", "part1_economics_009", "part1_economics_010", "part1_economics_011", "part1_economics_012", "part1_economics_013"]
}
```

---
