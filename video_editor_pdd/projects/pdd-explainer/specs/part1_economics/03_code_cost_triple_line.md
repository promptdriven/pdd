[Remotion]

# Section 1.3: Code Cost Triple Line — The Hidden Debt

**Tool:** Remotion
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 2:52 - 3:17

## Visual Description

A chart morphs from the sock economics chart into its code equivalent. The X-axis becomes a timeline from 2015 to 2025. The Y-axis reads "Cost (Developer Hours)." Three elements animate:

1. **Blue line** — "Cost to generate" — starts high (~40 hours), barely dips at Codex (2021), then plunges steeply starting at GPT-4/Claude (2023). Key dates appear as annotations on this line.
2. **Amber solid line** — "Immediate patch cost" — starts moderate (~8 hours), drops gradually with Copilot (2021), drops further with Cursor/Claude Code (2023-2024). This is what the viewer *feels* — each individual patch getting faster.
3. **Amber dashed line** — "Total cost (with debt)" — starts at ~12 hours and barely moves. Between the solid and dashed amber lines, a shaded area represents accumulated technical debt. As the solid line drops (patches get faster), the shaded debt area *expands upward* — revealing that faster patching creates more debt, not less.

The visual punch: the solid amber line drops, which *feels* like progress, but the dashed line (reality) barely budges. The gap between feeling and reality widens.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: horizontal at 5-hour intervals, `#1E293B` at 0.06; vertical at year markers, `#1E293B` at 0.06

### Chart/Visual Elements

#### Axes
- X-axis: 2015 to 2025, positioned at y: 820, `#475569` at 0.5, 2px
- Y-axis: 0 to 50 (developer hours), positioned at x: 180, `#475569` at 0.5, 2px
- Y-axis label: "Cost (Developer Hours)" — Inter, 13px, `#64748B` at 0.5, rotated -90°
- Year markers: "2015", "2017", "2019", "2021", "2023", "2025"

#### Line 1 — Generate Cost (blue, falling)
- Color: `#4A90D9`, 3px stroke
- Path: starts ~40 hours (2015), flat to 2021, barely dips at Codex, plunges from 2023
- Key date annotations along line:
  - "Codex" at 2021 — small pill badge, `#4A90D9` at 0.5
  - "GPT-4" at 2023 — pill badge
  - "Claude" at 2023.5 — pill badge
  - "Gemini" at 2024 — pill badge

#### Line 2 — Immediate Patch Cost (amber solid)
- Color: `#D9944A`, 3px solid stroke
- Path: starts ~8 hours (2015), gradual decline to ~3 hours (2025)
- Label: "Immediate patch cost" — Inter, 12px, `#D9944A` at 0.7

#### Line 3 — Total Cost with Debt (amber dashed)
- Color: `#D9944A`, 2px dashed stroke (8px dash, 6px gap)
- Path: starts ~12 hours (2015), barely declines to ~10 hours (2025)
- Label: "Total cost (with debt)" — Inter, 12px, `#D9944A` at 0.5

#### Debt Shaded Area
- Between amber solid and amber dashed lines
- Fill: `#D9944A` at 0.08, with subtle noise texture overlay at 0.02
- The area *widens* as the solid line drops — visually showing debt accumulation

#### Focus Callout
- Appears at frame 450: arrow pointing to the solid amber line with text "This is what you feel"
- At frame 540: arrow pointing to dashed amber line with text "This is what's real"
- Inter, 14px, `#E2E8F0` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Chart transitions from previous sock chart. Axes morph. Y-label changes to "Cost (Developer Hours)."
2. **Frame 30-120 (1-4s):** Blue "generate" line draws from left (2015) to right (2025). Key date badges appear as the line reaches each year.
3. **Frame 120-150 (4-5s):** Hold on generate line. The plunge at 2023 is dramatic.
4. **Frame 150-300 (5-10s):** Amber solid line draws. It drops gradually — this is the "faster patching" the viewer experiences. Simultaneously, the amber dashed line draws — barely moving.
5. **Frame 300-420 (10-14s):** Debt shaded area fills in between the two amber lines. The gap is visually startling — the feeling of progress (solid dropping) vs. reality (dashed flat).
6. **Frame 420-510 (14-17s):** "This is what you feel" callout appears on solid line. Beat. "This is what's real" callout appears on dashed line.
7. **Frame 510-600 (17-20s):** Camera pulls back slightly. All three elements visible. The blue line plunging below the amber dashed line at 2024 — generation becoming cheaper than total patch cost.
8. **Frame 600-750 (20-25s):** Hold on full chart. The argument is visual.

### Typography
- Axis labels: Inter, 12px, `#64748B` at 0.5
- Y-axis title: Inter, 13px, `#64748B` at 0.5
- Line labels: Inter, 12px, respective colors
- Date badges: Inter, 10px, bold (700), `#E2E8F0` on respective color pill backgrounds
- Callout text: Inter, 14px, `#E2E8F0` at 0.7

### Easing
- Line draw: `easeInOut(cubic)` — slower through flat sections, faster through steep drops
- Date badge appear: `easeOut(back(1.3))` scale pop, 10 frames
- Debt area fill: `easeOut(quad)` over 40 frames
- Callout fade-in: `easeOut(quad)` over 20 frames
- Camera pullback: `easeInOut(cubic)` over 60 frames

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot—you know these tools."
> "Look—each patch is getting faster. That's real. That's what you feel when you use these tools."
> "But watch the dashed line. The total cost. It's barely moving. Because even though each patch is faster, every patch still leaves residue. Technical debt."

Segment: `part1_003`

- **2:52** ("Now look at code"): Chart morphs from sock chart
- **2:55** ("For decades, generating new code was expensive"): Blue generate line draws, high and flat pre-2021
- **3:02** ("AI made patching faster too"): Amber solid line begins drawing, dropping
- **3:06** ("each patch is getting faster"): "This is what you feel" callout
- **3:10** ("But watch the dashed line"): Dashed line and debt area highlighted
- **3:14** ("every patch still leaves residue"): Debt area pulses

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Chart axes */}
    <Sequence from={0}>
      <ChartAxes
        xRange={[2015, 2025]} yRange={[0, 50]}
        xPos={180} yPos={820}
        gridColor="#1E293B" gridOpacity={0.06}
        axisColor="#475569" axisWidth={2}
        yLabel="Cost (Developer Hours)"
        xLabels={['2015','2017','2019','2021','2023','2025']}
        drawDuration={30}
      />
    </Sequence>

    {/* Blue line — Generate cost */}
    <Sequence from={30}>
      <AnimatedLine
        data={generateCostData} color="#4A90D9" width={3}
        drawDuration={90}
        label="Cost to generate" labelSize={12}
        dateBadges={[
          { year: 2021, text: 'Codex' },
          { year: 2023, text: 'GPT-4' },
          { year: 2023.5, text: 'Claude' },
          { year: 2024, text: 'Gemini' }
        ]}
      />
    </Sequence>

    {/* Amber solid — Immediate patch cost */}
    <Sequence from={150}>
      <AnimatedLine
        data={immediatePatchData} color="#D9944A" width={3}
        drawDuration={90} strokeStyle="solid"
        label="Immediate patch cost" labelSize={12}
      />
    </Sequence>

    {/* Amber dashed — Total cost with debt */}
    <Sequence from={150}>
      <AnimatedLine
        data={totalCostData} color="#D9944A" width={2}
        drawDuration={90} strokeStyle="dashed"
        dashArray={[8, 6]}
        label="Total cost (with debt)" labelSize={12}
        labelOpacity={0.5}
      />
    </Sequence>

    {/* Debt shaded area */}
    <Sequence from={300}>
      <ShadedArea
        between={[immediatePatchData, totalCostData]}
        range={[2015, 2025]} color="#D9944A" opacity={0.08}
        noiseTexture={0.02} fadeDuration={40}
      />
    </Sequence>

    {/* Callouts */}
    <Sequence from={420}>
      <ArrowCallout
        target={immediatePatchPoint2024}
        text="This is what you feel"
        color="#E2E8F0" opacity={0.7}
      />
    </Sequence>
    <Sequence from={510}>
      <ArrowCallout
        target={totalCostPoint2024}
        text="This is what's real"
        color="#E2E8F0" opacity={0.7}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "code_cost_triple_line",
  "xAxis": { "label": "Year", "range": [2015, 2025], "unit": "year" },
  "yAxis": { "label": "Cost (Developer Hours)", "range": [0, 50] },
  "series": [
    {
      "name": "Cost to generate",
      "color": "#4A90D9",
      "strokeWidth": 3,
      "strokeStyle": "solid",
      "dataPoints": [
        { "x": 2015, "y": 40 }, { "x": 2018, "y": 38 },
        { "x": 2021, "y": 35, "badge": "Codex" },
        { "x": 2022, "y": 30 },
        { "x": 2023, "y": 15, "badge": "GPT-4" },
        { "x": 2023.5, "y": 10, "badge": "Claude" },
        { "x": 2024, "y": 5, "badge": "Gemini" },
        { "x": 2025, "y": 2 }
      ]
    },
    {
      "name": "Immediate patch cost",
      "color": "#D9944A",
      "strokeWidth": 3,
      "strokeStyle": "solid",
      "dataPoints": [
        { "x": 2015, "y": 8 }, { "x": 2018, "y": 7.5 },
        { "x": 2021, "y": 6 }, { "x": 2023, "y": 4.5 },
        { "x": 2024, "y": 3.5 }, { "x": 2025, "y": 3 }
      ]
    },
    {
      "name": "Total cost (with debt)",
      "color": "#D9944A",
      "strokeWidth": 2,
      "strokeStyle": "dashed",
      "dataPoints": [
        { "x": 2015, "y": 12 }, { "x": 2018, "y": 11.5 },
        { "x": 2021, "y": 11 }, { "x": 2023, "y": 10.5 },
        { "x": 2024, "y": 10 }, { "x": 2025, "y": 10 }
      ]
    }
  ],
  "debtArea": {
    "between": ["Immediate patch cost", "Total cost (with debt)"],
    "color": "#D9944A",
    "opacity": 0.08
  },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part1_003"]
}
```

---
