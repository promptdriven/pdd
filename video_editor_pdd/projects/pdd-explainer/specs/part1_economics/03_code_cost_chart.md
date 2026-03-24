[Remotion]

# Section 1.3: Code Cost Chart — Generate vs Patch vs Total Debt

**Tool:** Remotion
**Duration:** ~42s (1260 frames @ 30fps)
**Timestamp:** 0:34 - 1:16

## Visual Description

A chart similar in style to the sock chart but now applied to code. Y-axis: "Cost (Developer Hours)". X-axis: years from 2000-2025. Three elements animate in sequence:

1. **Blue "Cost to generate" line** — starts high and flat (code generation was expensive for decades), then plunges steeply starting 2023 as GPT-4/Claude arrive. Key dates appear as markers: Codex (2021), GPT-4 (2023), Claude (2023), Gemini (2024).

2. **Amber solid "Immediate patch cost" line** — starts lower, drops post-2020 as Copilot helps. This is what developers *feel*.

3. **Amber dashed "Total cost (with debt)" line** — sits at the top, barely moves. A shaded area between the solid and dashed amber lines represents accumulated technical debt that grows as patching accelerates.

The key moment: as the camera "pulls back," the viewer sees the shaded debt area EXPANDING even as the immediate patch line drops. The gap between perception and reality becomes visible.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: `#1E293B` at 0.06, 80px horizontal, 60px vertical

### Chart/Visual Elements

#### Axes
- X-axis: 2000-2025, major ticks every 5 years
- X-axis label: "Year" — Inter, 11px, `#64748B` at 0.5
- Y-axis: "Cost (Developer Hours)" — Inter, 11px, `#64748B` at 0.5, rotated -90°
- Axis lines: `#334155` at 0.4, 1.5px
- Tick labels: JetBrains Mono, 10px, `#94A3B8` at 0.5

#### Line 1 — Cost to Generate (blue)
- Color: `#4A90D9`, 2.5px solid stroke
- Path: flat at ~85% from 2000-2021, barely dips at Codex (2021-2022), plunges steeply 2023-2025 to ~15%
- Glow: 6px Gaussian blur, `#4A90D9` at 0.12
- Label: "Cost to generate" — Inter, 11px, `#4A90D9` at 0.7

#### Key Date Markers (on blue line)
- "Codex" (2021): small circle 5px, `#4A90D9` at 0.6, label below
- "GPT-4" (2023): small circle 5px, `#4A90D9` at 0.8, label below
- "Claude" (2023.5): small circle 5px, `#4A90D9` at 0.8, label below
- "Gemini" (2024): small circle 5px, `#4A90D9` at 0.8, label below
- Labels: JetBrains Mono, 9px, `#4A90D9` at 0.6

#### Line 2 — Immediate Patch Cost (amber solid)
- Color: `#D9944A`, 2.5px solid stroke
- Path: starts at ~40% in 2000, fairly flat until 2020, then drops to ~20% by 2025
- Glow: 6px Gaussian blur, `#D9944A` at 0.12
- Label: "Immediate patch cost" — Inter, 11px, `#D9944A` at 0.7

#### Line 3 — Total Cost with Debt (amber dashed)
- Color: `#D9944A`, 2px dashed stroke (dash: 8, gap: 4)
- Path: starts at ~55% in 2000, rises gently to ~60% by 2025 — barely moves
- Glow: none
- Label: "Total cost (with debt)" — Inter, 11px, `#D9944A` at 0.5

#### Debt Shading (between solid and dashed amber)
- Fill: `#D9944A` at 0.06 → 0.10 (deepens as gap widens post-2020)
- The area EXPANDS as immediate cost drops — this is the key visual paradox

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Axes draw in. Grid fades in.
2. **Frame 40-80 (1.33-2.67s):** "Now look at code." — chart title area. Y-axis label appears.
3. **Frame 80-240 (2.67-8s):** Blue "generate" line draws from 2000 rightward. Flat for years. Key date markers appear as line reaches each year. Codex barely dips the line. GPT-4/Claude cause steep plunge.
4. **Frame 240-420 (8-14s):** Amber solid "immediate patch" line draws. Drops post-2020 as Copilot arrives. This validates the viewer's experience.
5. **Frame 420-480 (14-16s):** Focus on the dropping immediate line — a brief "validation" moment. Subtle highlight glow on the amber solid line.
6. **Frame 480-660 (16-22s):** Amber dashed "total cost" line draws across. Shaded debt area fills between the two amber lines. The area EXPANDS visibly even as the solid line drops.
7. **Frame 660-900 (22-30s):** "Camera pulls back" — the chart viewport widens slightly (scale 1.0 → 0.92) revealing the full picture. The shaded area dominates. The gap between what you feel and what's real is stark.
8. **Frame 900-1260 (30-42s):** Hold on complete chart. Lines continue subtly animating (the generate line's glow pulses).

### Typography
- Axis labels: Inter, 11px, `#64748B` at 0.5
- Tick labels: JetBrains Mono, 10px, `#94A3B8` at 0.5
- Line labels: Inter, 11px, respective colors
- Key date labels: JetBrains Mono, 9px, `#4A90D9` at 0.6

### Easing
- Axis draw: `easeOut(cubic)` over 30 frames
- Line draw: `easeInOut(quad)` continuous
- Key date markers: `easeOut(back)` over 12 frames
- Debt shading fill: `easeOut(quad)` progressive
- Viewport scale: `easeInOut(cubic)` over 60 frames
- Line glow pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot—you know these tools."
> "Each patch is getting faster. That's real. That's what you feel when you use these tools."
> "But watch the dashed line. The total cost. It's barely moving."
> "Because even though each patch is faster, every patch still leaves residue."

Segments: `part1_economics_008` through `part1_economics_013`

- **0:34** ("Now look at code."): Chart axes begin drawing
- **0:36** ("For decades, generating"): Blue line starts drawing, flat for years
- **0:50** ("something else happened"): Amber solid line begins, drops post-2020
- **1:00** ("Each patch is getting faster"): Focus/highlight on dropping amber line
- **1:06** ("But watch the dashed line"): Dashed line and debt shading appear
- **1:11** ("even though each patch is faster"): Viewport pulls back revealing full picture

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1260}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <ChartGrid hSpacing={80} vSpacing={60} color="#1E293B" opacity={0.06} />

    {/* Axes */}
    <AnimatedAxis axis="x" from={2000} to={2025}
      majorTick={5} color="#334155" opacity={0.4}
      drawDuration={30} />
    <AnimatedAxis axis="y" label="Cost (Developer Hours)"
      color="#334155" opacity={0.4} drawDuration={30} />

    {/* Blue generate line */}
    <Sequence from={80}>
      <AnimatedLine data={generateCostData} color="#4A90D9"
        width={2.5} glow={{ blur: 6, opacity: 0.12 }}
        drawDuration={520} />
      <KeyDateMarkers dates={keyDates} color="#4A90D9"
        font="JetBrains Mono" size={9} />
    </Sequence>

    {/* Amber solid — immediate patch */}
    <Sequence from={240}>
      <AnimatedLine data={immediatePatchData} color="#D9944A"
        width={2.5} glow={{ blur: 6, opacity: 0.12 }}
        drawDuration={180} />
    </Sequence>

    {/* Amber dashed — total cost */}
    <Sequence from={480}>
      <AnimatedLine data={totalCostData} color="#D9944A"
        width={2} dashArray={[8, 4]}
        drawDuration={120} />
    </Sequence>

    {/* Debt shading */}
    <Sequence from={480}>
      <AreaBetween upper={totalCostData} lower={immediatePatchData}
        color="#D9944A" opacity={0.08}
        fillDuration={180} />
    </Sequence>

    {/* Viewport pull-back */}
    <Sequence from={660}>
      <ScaleTransition from={1.0} to={0.92} duration={60}
        origin="center" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "code_cost_triple_line",
  "chartType": "triple_line",
  "xAxis": { "label": "Year", "range": [2000, 2025], "majorTick": 5 },
  "yAxis": { "label": "Cost (Developer Hours)", "range": [0, 100] },
  "series": [
    {
      "id": "generate_cost",
      "label": "Cost to generate",
      "color": "#4A90D9",
      "style": "solid",
      "dataPoints": [
        { "x": 2000, "y": 85 }, { "x": 2005, "y": 85 },
        { "x": 2010, "y": 84 }, { "x": 2015, "y": 83 },
        { "x": 2020, "y": 82 }, { "x": 2021, "y": 78 },
        { "x": 2022, "y": 75 }, { "x": 2023, "y": 50 },
        { "x": 2024, "y": 25 }, { "x": 2025, "y": 15 }
      ]
    },
    {
      "id": "immediate_patch",
      "label": "Immediate patch cost",
      "color": "#D9944A",
      "style": "solid",
      "dataPoints": [
        { "x": 2000, "y": 40 }, { "x": 2005, "y": 39 },
        { "x": 2010, "y": 38 }, { "x": 2015, "y": 37 },
        { "x": 2020, "y": 35 }, { "x": 2021, "y": 32 },
        { "x": 2022, "y": 28 }, { "x": 2023, "y": 24 },
        { "x": 2024, "y": 22 }, { "x": 2025, "y": 20 }
      ]
    },
    {
      "id": "total_cost_debt",
      "label": "Total cost (with debt)",
      "color": "#D9944A",
      "style": "dashed",
      "dataPoints": [
        { "x": 2000, "y": 55 }, { "x": 2005, "y": 55 },
        { "x": 2010, "y": 56 }, { "x": 2015, "y": 56 },
        { "x": 2020, "y": 57 }, { "x": 2021, "y": 57 },
        { "x": 2022, "y": 58 }, { "x": 2023, "y": 59 },
        { "x": 2024, "y": 60 }, { "x": 2025, "y": 60 }
      ]
    }
  ],
  "keyDates": [
    { "year": 2021, "label": "Codex" },
    { "year": 2023, "label": "GPT-4" },
    { "year": 2023.5, "label": "Claude" },
    { "year": 2024, "label": "Gemini" }
  ],
  "debtShading": { "between": ["total_cost_debt", "immediate_patch"], "color": "#D9944A" },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_008", "part1_economics_009", "part1_economics_010", "part1_economics_011", "part1_economics_012", "part1_economics_013"]
}
```

---
