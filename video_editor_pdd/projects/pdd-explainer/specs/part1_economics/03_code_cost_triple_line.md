[Remotion]

# Section 1.2: Code Cost Triple-Line Chart — Generate vs Patch vs Total

**Tool:** Remotion
**Duration:** ~35s (1050 frames @ 30fps)
**Timestamp:** 2:52 - 3:27

## Visual Description

The sock economics chart morphs into a new chart about code. The axes relabel: Y-axis becomes "Cost (Developer Hours)" and X-axis becomes a timeline from 2015 to 2025. Three elements animate in sequence:

1. **Blue line** ("Cost to generate") — starts high, barely dips at Codex (2021), then plunges steeply starting at GPT-4/Claude (2023).
2. **Amber solid line** ("Immediate patch cost") — starts moderate, drops as Copilot arrives (2021), continues dropping with Cursor/Claude Code.
3. **Amber dashed line** ("Total cost with debt") — sits at the top of a shaded area above the solid amber line. This dashed line barely moves even as patching gets cheaper.

The shaded area between the solid and dashed amber lines represents accumulated technical debt. As the solid line drops (patches get faster), the shaded area EXPANDS — visually revealing the paradox that faster patching creates more debt.

Key AI milestones appear as subtle vertical markers: Codex (2021), Copilot (2022), GPT-4/Claude (2023), Cursor/Claude Code (2024).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`
- Chart area: 280px left margin, 100px right, 140px top, 120px bottom

### Chart/Visual Elements

#### Axes
- X-axis: 2015–2025, major ticks every 2 years, minor ticks every year
- X-axis label: "Year" — Inter, 12px, `#94A3B8` at 0.3
- Y-axis: 0–20 (developer hours), major ticks at 5-hour intervals
- Y-axis label: "Cost (Developer Hours)" — Inter, 12px, `#94A3B8` at 0.3
- Axis lines: `#334155` at 0.25, 1px
- Grid lines: horizontal only, `#334155` at 0.08, 1px dashed

#### AI Milestone Markers
- Vertical dashed lines at Codex (2021), Copilot (2022), GPT-4/Claude (2023), Cursor/Claude Code (2024)
- Line: `#94A3B8` at 0.12, 1px dashed
- Labels: Inter, 9px, `#94A3B8` at 0.3, rotated -45°, positioned at top

#### Line 1 — Cost to Generate (Blue)
- Color: `#4A90D9`, 3px stroke
- Data: ~18hrs in 2015, ~17hrs in 2020, ~16hrs at Codex, then plunges: ~10hrs at GPT-4, ~4hrs by 2025
- Label: "Cost to generate" — Inter, 12px, `#4A90D9` at 0.7

#### Line 2 — Immediate Patch Cost (Amber Solid)
- Color: `#D9944A`, 3px stroke, solid
- Data: ~8hrs in 2015, ~7hrs in 2020, drops to ~5hrs with Copilot, ~3hrs with Cursor, ~2hrs by 2025
- Label: "Immediate patch cost" — Inter, 12px, `#D9944A` at 0.7

#### Line 3 — Total Cost with Debt (Amber Dashed)
- Color: `#D9944A`, 2px stroke, dashed (8px dash, 4px gap)
- Data: ~14hrs in 2015, stays ~13-14hrs throughout — barely moves
- Label: "Total cost (with debt)" — Inter, 12px, `#D9944A` at 0.5

#### Debt Shaded Area
- Between solid amber and dashed amber lines
- Color: `#D9944A` at 0.08, expanding as the solid line drops
- Subtle pulse animation at full extent

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous sock chart morphs — axes relabel, grid adjusts. Smooth transformation.
2. **Frame 30-60 (1-2s):** AI milestone markers fade in as subtle vertical dashed lines.
3. **Frame 60-180 (2-6s):** Blue "generate" line draws left-to-right. Nearly flat until 2021, then dips slightly at Codex, plunges at GPT-4 (2023).
4. **Frame 180-300 (6-10s):** Amber solid "immediate patch" line draws. Drops at Copilot, continues dropping.
5. **Frame 300-420 (10-14s):** Amber dashed "total cost" line draws. Stays nearly flat — the key reveal.
6. **Frame 420-540 (14-18s):** Shaded debt area fills between the two amber lines. The gap is large and growing.
7. **Frame 540-720 (18-24s):** Hold. Debt area pulses gently. The visual contrast between the dropping solid line and flat dashed line is stark.
8. **Frame 720-1050 (24-35s):** Chart holds for narration about the paradox.

### Typography
- Axis labels: Inter, 12px, `#94A3B8` at 0.3
- Tick labels: Inter, 10px, `#94A3B8` at 0.25
- Milestone labels: Inter, 9px, `#94A3B8` at 0.3
- Line labels: Inter, 12px, respective colors
- Terminal breadcrumb: none (focus is on data)

### Easing
- Chart morph: `easeInOut(cubic)` over 30 frames
- Line draws: `linear` (steady reveal)
- Milestone markers: `easeOut(quad)` fade-in over 10 frames
- Debt area fill: `easeOut(quad)` over 30 frames
- Debt area pulse: `easeInOut(sine)` on 60-frame cycle, opacity 0.08 → 0.12 → 0.08

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot — you know these tools."
> "Look — each patch is getting faster. That's real. That's what you feel when you use these tools."
> "But watch the dashed line. The total cost. It's barely moving."
> "Because even though each patch is faster, every patch still leaves residue. Technical debt."

Segments: `part1_economics_005`, `part1_economics_006`, `part1_economics_008`, `part1_economics_009`, `part1_economics_011`, `part1_economics_012`

- **2:52** ("Now look at code"): Chart morph begins
- **2:54** ("For decades"): Blue "generate" line draws, high and flat in early years
- **3:04** ("AI made patching faster"): Amber solid line draws, drops at Copilot
- **3:10** ("each patch is getting faster"): Focus on dropping solid amber line
- **3:16** ("watch the dashed line"): Dashed line revealed — barely moves
- **3:20** ("every patch still leaves residue"): Debt shaded area fills, expanding

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1050}>
  <AbsoluteFill style={{ backgroundColor: '#0D1117' }}>
    {/* Chart morph from sock chart */}
    <Sequence from={0} durationInFrames={30}>
      <ChartMorph
        fromAxes={sockChartAxes} toAxes={codeChartAxes}
        duration={30} easing="easeInOutCubic"
      />
    </Sequence>

    {/* AI milestone markers */}
    <Sequence from={30}>
      <MilestoneMarkers
        milestones={[
          { x: 2021, label: "Codex" },
          { x: 2022, label: "Copilot" },
          { x: 2023, label: "GPT-4 / Claude" },
          { x: 2024, label: "Cursor / Claude Code" }
        ]}
        lineColor="#94A3B8" lineOpacity={0.12}
        labelFont="Inter" labelSize={9}
      />
    </Sequence>

    {/* Blue: Cost to generate */}
    <Sequence from={60}>
      <AnimatedLine
        data={generateCostData} color="#4A90D9" strokeWidth={3}
        label="Cost to generate" drawDuration={120}
      />
    </Sequence>

    {/* Amber solid: Immediate patch cost */}
    <Sequence from={180}>
      <AnimatedLine
        data={immediatePatchData} color="#D9944A" strokeWidth={3}
        label="Immediate patch cost" drawDuration={120}
      />
    </Sequence>

    {/* Amber dashed: Total cost with debt */}
    <Sequence from={300}>
      <AnimatedLine
        data={totalCostDebtData} color="#D9944A" strokeWidth={2}
        dashArray={[8, 4]}
        label="Total cost (with debt)" drawDuration={120}
      />
    </Sequence>

    {/* Debt shaded area */}
    <Sequence from={420}>
      <ShadedArea
        upperLine={totalCostDebtData} lowerLine={immediatePatchData}
        color="#D9944A" opacity={0.08}
        fillDuration={120}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartType": "triple_line_debt_reveal",
  "xAxis": {
    "label": "Year",
    "range": [2015, 2025],
    "majorInterval": 2,
    "minorInterval": 1
  },
  "yAxis": {
    "label": "Cost (Developer Hours)",
    "range": [0, 20],
    "majorInterval": 5
  },
  "milestones": [
    { "x": 2021, "label": "Codex" },
    { "x": 2022, "label": "Copilot" },
    { "x": 2023, "label": "GPT-4 / Claude" },
    { "x": 2024, "label": "Cursor / Claude Code" }
  ],
  "series": [
    {
      "id": "cost_to_generate",
      "label": "Cost to generate",
      "color": "#4A90D9",
      "strokeWidth": 3,
      "style": "solid",
      "data": [
        { "x": 2015, "y": 18 }, { "x": 2018, "y": 17.5 },
        { "x": 2020, "y": 17 }, { "x": 2021, "y": 16 },
        { "x": 2022, "y": 14 }, { "x": 2023, "y": 10 },
        { "x": 2024, "y": 6 }, { "x": 2025, "y": 4 }
      ]
    },
    {
      "id": "immediate_patch_cost",
      "label": "Immediate patch cost",
      "color": "#D9944A",
      "strokeWidth": 3,
      "style": "solid",
      "data": [
        { "x": 2015, "y": 8 }, { "x": 2018, "y": 7.5 },
        { "x": 2020, "y": 7 }, { "x": 2021, "y": 6 },
        { "x": 2022, "y": 5 }, { "x": 2023, "y": 4 },
        { "x": 2024, "y": 3 }, { "x": 2025, "y": 2 }
      ]
    },
    {
      "id": "total_cost_with_debt",
      "label": "Total cost (with debt)",
      "color": "#D9944A",
      "strokeWidth": 2,
      "style": "dashed",
      "data": [
        { "x": 2015, "y": 14 }, { "x": 2018, "y": 14 },
        { "x": 2020, "y": 13.5 }, { "x": 2021, "y": 13.5 },
        { "x": 2022, "y": 13 }, { "x": 2023, "y": 13 },
        { "x": 2024, "y": 13 }, { "x": 2025, "y": 13 }
      ]
    }
  ],
  "debtShadedArea": {
    "upperSeries": "total_cost_with_debt",
    "lowerSeries": "immediate_patch_cost",
    "color": "#D9944A",
    "opacity": 0.08
  },
  "backgroundColor": "#0D1117",
  "narrationSegments": [
    "part1_economics_005", "part1_economics_006",
    "part1_economics_008", "part1_economics_009",
    "part1_economics_011", "part1_economics_012"
  ]
}
```

---
