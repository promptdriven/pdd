[Remotion]

# Section 1.3: Code Cost Chart — Generate vs. Patch vs. Total Debt

**Tool:** Remotion
**Duration:** ~55s (1650 frames @ 30fps)
**Timestamp:** 0:48 - 1:43

## Visual Description

The core economic chart of the entire video. Three elements plotted from 2000 to 2026:

1. **"Cost to generate" (blue line, `#4A90D9`):** Starts high. Barely dips at Codex (2021). Plunges steeply starting at GPT-4/Claude (2023).
2. **"Immediate patch cost" (amber solid line, `#D9944A`):** Starts moderate-high. Begins dropping post-2020 as Copilot arrives.
3. **"Total cost with debt" (amber dashed line, `#D9944A`):** Stays near the top, barely moving. A shaded area between the solid and dashed amber lines represents accumulated technical debt — the gap between what developers feel (solid) and what's real (dashed).

Key dates appear as vertical markers on the blue line: Codex (2021), GPT-4 (2023), Claude (2023), Gemini (2024). The chart visually demonstrates the central argument: individual tasks feel faster, but total cost barely moves.

This spec covers the initial chart draw and the "each patch is getting faster" validation beat before pulling back to reveal the debt expansion.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal at 150px intervals, `#1E293B` at 0.08

### Chart/Visual Elements

#### Axes
- X-axis: 2000 to 2026, labeled at key dates, `#94A3B8` at 0.6, Inter 14px
- Y-axis: "Cost (Developer Hours)", `#94A3B8` at 0.6, Inter 14px
- Axis lines: `#334155`, 1.5px

#### Lines
- Generate (blue): `#4A90D9`, 3px solid — high plateau 2000-2021, slight dip 2021-2022, steep plunge 2023-2026
- Immediate patch (amber solid): `#D9944A`, 3px solid — moderate, drops post-2020
- Total cost with debt (amber dashed): `#D9944A`, 2.5px dashed (8px dash, 6px gap) — near top, barely moves

#### Shaded Debt Area
- Fill between solid and dashed amber lines: `#D9944A` at 0.12
- Expands upward as the solid line drops — gap widens over time

#### Date Markers (on blue line)
- "Codex" (2021): vertical dashed line `#64748B`, label Inter 12px
- "GPT-4" (2023): vertical dashed line, label
- "Claude" (2023.5): vertical dashed line, label
- "Gemini" (2024): vertical dashed line, label

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Axes draw in. Y-axis label: "Cost (Developer Hours)".
2. **Frame 45-180 (1.5-6s):** Blue "generate" line draws from left — high plateau from 2000 to 2021. Date markers appear as the line passes each year.
3. **Frame 180-300 (6-10s):** Blue line barely dips at Codex (2021-2022). Then GPT-4/Claude markers appear (2023) and the line plunges steeply.
4. **Frame 300-450 (10-15s):** Amber solid line draws — moderate cost, stable through 2010s. Post-2020, it begins dropping as Copilot helps.
5. **Frame 450-540 (15-18s):** Focus pulse on the solid amber line dropping. This validates the viewer's experience. Subtle glow on the line.
6. **Frame 540-600 (18-20s):** Amber dashed line draws at the top. Shaded debt area fills between solid and dashed.
7. **Frame 600-900 (20-30s):** Camera "pulls back" (chart scale adjusts). The debt area EXPANDS visibly. Dashed line barely moves while solid line drops. The gap becomes stark.
8. **Frame 900-1650 (30-55s):** Hold with debt area visible. Chart remains on screen for research annotation overlays (next specs).

### Typography
- Axis labels: Inter, 14px, regular (400), `#94A3B8` at 0.6
- Date markers: Inter, 12px, regular (400), `#94A3B8` at 0.8
- Line legend: Inter, 14px, semi-bold (600), respective colors

### Easing
- Line draw: `easeInOut(cubic)`
- Blue line plunge: `easeIn(quad)` — accelerating descent
- Debt area fill: `easeOut(quad)` over 60 frames
- Focus pulse: `easeInOut(sine)` on 30-frame cycle
- Camera pullback: `easeInOut(cubic)` over 90 frames

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot — you know these tools."
> "Look — each patch is getting faster. That's real. That's what you feel when you use these tools."
> "But watch the dashed line. The total cost. It's barely moving. Because even though each patch is faster, every patch still leaves residue."

Segments: `part1_economics_006`, `part1_economics_007`, `part1_economics_008`, `part1_economics_009`

- **47.54s** (seg 006): Chart axes draw — "Now look at code"
- **50.0s**: Blue line begins drawing — "For decades, generating new code was expensive"
- **61.86s** (seg 006 ends): Blue line reaching Codex
- **62.08s** (seg 007): "But something else happened" — amber solid line draws, Copilot drops it
- **78.54s** (seg 007 ends): Focus on dropping solid amber line
- **78.70s** (seg 008): "Look — each patch is getting faster" — validation pulse
- **86.00s** (seg 008 ends): Transition to pullback
- **86.24s** (seg 009): "But watch the dashed line" — camera pulls back, debt area visible
- **101.78s** (seg 009 ends): Debt expansion fully visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1650}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <HorizontalGrid spacing={150} color="#1E293B" opacity={0.08} />

    {/* Axes */}
    <Sequence from={0}>
      <DrawAxes
        xRange={[2000, 2026]}
        yLabel="Cost (Developer Hours)"
        color="#334155" labelColor="#94A3B8"
      />
    </Sequence>

    {/* Blue "generate" line */}
    <Sequence from={45}>
      <AnimatedLine data={generateCostData}
        color="#4A90D9" strokeWidth={3}
        drawDuration={255} easing="easeInOutCubic" />
    </Sequence>

    {/* Date markers */}
    <Sequence from={150}>
      <DateMarker year={2021} label="Codex" />
      <DateMarker year={2023} label="GPT-4" />
      <DateMarker year={2023.5} label="Claude" />
      <DateMarker year={2024} label="Gemini" />
    </Sequence>

    {/* Amber solid "immediate patch" line */}
    <Sequence from={300}>
      <AnimatedLine data={immediatePatchData}
        color="#D9944A" strokeWidth={3}
        drawDuration={150} />
    </Sequence>

    {/* Validation pulse */}
    <Sequence from={450}>
      <LinePulse target="immediate_patch"
        color="#D9944A" glowRadius={8}
        duration={90} />
    </Sequence>

    {/* Dashed "total cost" line + debt area */}
    <Sequence from={540}>
      <AnimatedLine data={totalCostData}
        color="#D9944A" strokeWidth={2.5}
        dashArray="8 6" drawDuration={60} />
      <ShadedArea
        upperBound={totalCostData}
        lowerBound={immediatePatchData}
        color="#D9944A" opacity={0.12}
        fillDuration={60}
      />
    </Sequence>

    {/* Camera pullback */}
    <Sequence from={600}>
      <ScaleTransition from={1.0} to={0.85}
        duration={90} easing="easeInOutCubic" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "multi_line_chart",
  "chartId": "code_cost_generate_vs_patch",
  "xAxis": { "label": "Year", "range": [2000, 2026] },
  "yAxis": { "label": "Cost (Developer Hours)" },
  "series": [
    {
      "id": "generate_cost",
      "label": "Cost to generate",
      "color": "#4A90D9",
      "strokeStyle": "solid",
      "data": [
        { "x": 2000, "y": 0.9 }, { "x": 2010, "y": 0.88 },
        { "x": 2020, "y": 0.85 }, { "x": 2021, "y": 0.82 },
        { "x": 2022, "y": 0.78 }, { "x": 2023, "y": 0.65 },
        { "x": 2024, "y": 0.35 }, { "x": 2025, "y": 0.18 },
        { "x": 2026, "y": 0.1 }
      ]
    },
    {
      "id": "immediate_patch",
      "label": "Immediate patch cost",
      "color": "#D9944A",
      "strokeStyle": "solid",
      "data": [
        { "x": 2000, "y": 0.55 }, { "x": 2010, "y": 0.52 },
        { "x": 2020, "y": 0.48 }, { "x": 2021, "y": 0.42 },
        { "x": 2022, "y": 0.35 }, { "x": 2023, "y": 0.28 },
        { "x": 2024, "y": 0.22 }, { "x": 2025, "y": 0.18 },
        { "x": 2026, "y": 0.15 }
      ]
    },
    {
      "id": "total_cost_debt",
      "label": "Total cost (with debt)",
      "color": "#D9944A",
      "strokeStyle": "dashed",
      "data": [
        { "x": 2000, "y": 0.6 }, { "x": 2010, "y": 0.62 },
        { "x": 2020, "y": 0.65 }, { "x": 2021, "y": 0.66 },
        { "x": 2022, "y": 0.68 }, { "x": 2023, "y": 0.7 },
        { "x": 2024, "y": 0.72 }, { "x": 2025, "y": 0.73 },
        { "x": 2026, "y": 0.74 }
      ]
    }
  ],
  "shadedArea": {
    "upper": "total_cost_debt",
    "lower": "immediate_patch",
    "color": "#D9944A",
    "opacity": 0.12,
    "label": "Technical debt"
  },
  "dateMarkers": ["Codex (2021)", "GPT-4 (2023)", "Claude (2023)", "Gemini (2024)"],
  "narrationSegments": ["part1_economics_006", "part1_economics_007", "part1_economics_008", "part1_economics_009"]
}
```

---
