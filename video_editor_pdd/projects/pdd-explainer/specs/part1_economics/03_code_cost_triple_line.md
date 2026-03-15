[Remotion]

# Section 1.3: Code Cost — Triple Line Chart with Debt Area

**Tool:** Remotion
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 2:45 - 3:10

## Visual Description
The core economics visualization of Part 1. A line chart with three elements tracking code costs over time (2015–2025+): a blue "Cost to Generate" line (starts high, plunges at GPT-4/Claude), an amber solid "Immediate Patch Cost" line (starts low, drops slightly with Copilot), and a dashed amber "Total Cost (with debt)" line at the top that barely moves. A shaded area between the solid and dashed amber lines represents accumulated technical debt — it expands as patching gets faster. Key AI milestones (Codex, GPT-4, Claude, Gemini) appear as labels on the generation line. The chart morphs through several states as the narration progresses.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.05)`, 6 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1400px wide x 620px tall, left margin 280px, top margin 180px
- **X-Axis:** Years 2015–2026, labeled every year, white `#FFFFFF` at 0.5 opacity
- **Y-Axis:** "Cost (Developer Hours)" — labeled at 0, 5, 10, 15, 20, white `#FFFFFF` at 0.5 opacity
- **Generate Line:** `#4A90D9` (cool blue), 3px stroke, starts at ~18 (2015), stays flat until 2021, barely dips at Codex (2021-22), then plunges steeply from 2023 onward to ~2 by 2025
- **Immediate Patch Line (solid):** `#D9944A` (warm amber), 3px solid stroke, starts at ~6 (2015), drops gradually to ~4 by 2020, then to ~3 with Copilot by 2023
- **Total Cost Line (dashed):** `#D9944A` (warm amber), 2px dashed stroke (dash: 8px, gap: 6px), starts at ~14 (2015), stays relatively flat at ~13-14 through 2025
- **Debt Shaded Area:** Between solid and dashed amber lines, fill `rgba(217, 148, 74, 0.15)`, expands visually as solid line drops
- **AI Milestone Labels:** Small pill-shaped badges along the blue line:
  - "Codex" at 2021, tiny dip
  - "GPT-4" at 2023, steep drop begins
  - "Claude" at 2023.5
  - "Gemini" at 2024
- **Crossing Moment:** Blue line crosses below dashed amber line at ~2024.5, then crosses below solid amber at ~2025

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Axes draw in. Labels fade in. Chart title "Code Economics" appears top-center
2. **Frame 30-120 (1.0-4.0s):** All three lines draw simultaneously from 2015 rightward to 2020. Debt area fills in behind amber lines as they draw. Lines are relatively stable in this era
3. **Frame 120-180 (4.0-6.0s):** Lines continue drawing to 2021-22. "Codex" badge pops in at the blue line's slight dip. Immediate patch line starts dropping (Copilot effect)
4. **Frame 180-350 (6.0-11.67s):** Lines draw through 2023-24. Blue line plunges dramatically. "GPT-4" and "Claude" badges pop in. Debt area between amber lines EXPANDS as solid drops but dashed stays flat. Camera subtly pulls back to reveal growing gap
5. **Frame 350-450 (11.67-15.0s):** Blue line crosses below dashed line — crossing pulse highlight. "Gemini" badge appears. Text annotation: "Generation cheaper than total patch cost"
6. **Frame 450-550 (15.0-18.33s):** Blue line continues to cross below even the solid immediate line. Second crossing pulse. Annotation: "We are here."
7. **Frame 550-650 (18.33-21.67s):** Debt area pulses gently. Annotation appears pointing to the expanding gap: "Faster patching → faster growth → faster rot"
8. **Frame 650-750 (21.67-25.0s):** Hold final state. All annotations visible. The stark contrast between the three lines is clear

### Typography
- Chart Title: Inter, 28px, semi-bold (600), `#FFFFFF`, opacity 0.9
- Axis Labels: Inter, 14px, regular (400), `#FFFFFF`, opacity 0.5
- AI Milestone Badges: Inter, 13px, semi-bold (600), white on `rgba(74,144,217,0.3)` pill background, border-radius 10px, padding 4px 10px
- Annotations: Inter, 18px, regular (400), `#FFFFFF`, opacity 0.85
- "We are here" Label: Inter, 22px, bold (700), `#FFFFFF`

### Easing
- Axis draw: `easeOut(cubic)`
- Line draw: `linear` (time-proportional)
- Blue line plunge (2023+): `easeIn(quad)` for acceleration feel
- Badge pop: `easeOut(back(1.3))`
- Crossing pulse: `easeOut(quad)`
- Debt area expand: `linear` (matches line draw)
- Annotations: `easeOut(quad)`

## Narration Sync
> "Now look at code."
> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."
> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot — you know these tools."
> "Look — each patch is getting faster. That's real. That's what you feel when you use these tools."
> "But watch the dashed line. The total cost. It's barely moving."
> "Because even though each patch is faster, every patch still leaves residue. Technical debt."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  {/* Axes */}
  <Sequence from={0} durationInFrames={30}>
    <AnimatedAxis
      xRange={[2015, 2026]}
      yRange={[0, 20]}
      xLabel="Year"
      yLabel="Cost (Developer Hours)"
    />
  </Sequence>

  {/* Lines and Debt Area */}
  <Sequence from={30} durationInFrames={520}>
    <DebtShadedArea
      upperLine={totalCostData}
      lowerLine={immediatePatchData}
      fill="rgba(217, 148, 74, 0.15)"
    />
    <AnimatedLine data={generateCostData} color="#4A90D9" strokeWidth={3} />
    <AnimatedLine data={immediatePatchData} color="#D9944A" strokeWidth={3} />
    <DashedLine data={totalCostData} color="#D9944A" strokeWidth={2} />
  </Sequence>

  {/* AI Milestone Badges */}
  <Sequence from={120}><Badge label="Codex" x={2021} /></Sequence>
  <Sequence from={200}><Badge label="GPT-4" x={2023} /></Sequence>
  <Sequence from={230}><Badge label="Claude" x={2023.5} /></Sequence>
  <Sequence from={380}><Badge label="Gemini" x={2024} /></Sequence>

  {/* Crossing Highlights */}
  <Sequence from={350}>
    <CrossingPulse x={2024.5} label="Generation cheaper than total patch cost" />
  </Sequence>
  <Sequence from={450}>
    <CrossingPulse x={2025} label="We are here." />
  </Sequence>

  {/* Debt Annotation */}
  <Sequence from={550}>
    <Annotation text="Faster patching → faster growth → faster rot" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "xAxis": { "label": "Year", "range": [2015, 2026], "tickInterval": 1 },
  "yAxis": { "label": "Cost (Developer Hours)", "range": [0, 20] },
  "generateCost": [
    { "year": 2015, "value": 18 },
    { "year": 2018, "value": 17.5 },
    { "year": 2020, "value": 17 },
    { "year": 2021, "value": 16 },
    { "year": 2022, "value": 15 },
    { "year": 2023, "value": 10 },
    { "year": 2023.5, "value": 6 },
    { "year": 2024, "value": 4 },
    { "year": 2025, "value": 2 }
  ],
  "immediatePatchCost": [
    { "year": 2015, "value": 6 },
    { "year": 2018, "value": 5.5 },
    { "year": 2020, "value": 5 },
    { "year": 2022, "value": 4.5 },
    { "year": 2023, "value": 3.5 },
    { "year": 2025, "value": 3 }
  ],
  "totalCostWithDebt": [
    { "year": 2015, "value": 14 },
    { "year": 2018, "value": 14 },
    { "year": 2020, "value": 13.5 },
    { "year": 2022, "value": 13.5 },
    { "year": 2023, "value": 13.5 },
    { "year": 2025, "value": 13 }
  ],
  "milestones": [
    { "label": "Codex", "year": 2021 },
    { "label": "GPT-4", "year": 2023 },
    { "label": "Claude", "year": 2023.5 },
    { "label": "Gemini", "year": 2024 }
  ],
  "backgroundColor": "#0F172A"
}
```

---
