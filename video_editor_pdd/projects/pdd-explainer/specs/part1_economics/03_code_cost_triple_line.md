[Remotion]

# Section 1.2: Code Cost — Triple-Line Economic Chart

**Tool:** Remotion
**Duration:** ~46s
**Timestamp:** 0:44 – 1:30

## Visual Description
The central economic argument of Part 1, visualized as an animated triple-line chart. Three elements track the cost of code over time (2015–2026): a blue "Cost to Generate" line (starting high, plunging after 2023), a solid amber "Immediate Patch Cost" line (dropping steadily), and a dashed amber "Total Cost (with Debt)" line that barely moves. The shaded area between the two amber lines represents hidden technical debt. Key AI milestones (Codex, GPT-4, Claude) appear on the blue line. The chart reveals the gap between what developers feel (dropping patch cost) and reality (flat total cost).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F1923 (dark blue-black)
- Grid lines: Horizontal at 25%, 50%, 75% — #FFFFFF at 5% opacity

### Chart/Visual Elements
- **Chart area:** 1400×600px, centered
- **X-axis:** Years 2015–2026, ticks at each year
- **Y-axis:** "Cost (Developer Hours)" — 0 to 40 hours, ticks at 10-hour intervals
- **Blue "Generate" line:** #4A90D9, 3px solid — starts at ~35h, barely dips at 2021 (Codex), plunges steeply from 2023 (GPT-4/Claude) to ~3h by 2026
- **Solid amber "Immediate Patch" line:** #D9944A, 3px solid — starts at ~8h, drops to ~3h by 2026
- **Dashed amber "Total Cost (with Debt)" line:** #D9944A, 3px dashed (8px dash, 6px gap) — starts at ~25h, stays nearly flat at ~22–24h
- **Debt shaded area:** Between solid and dashed amber lines, #D9944A at 10% opacity, with subtle animated noise texture
- **AI milestone markers:** Small circles on the blue line with labels:
  - 2021: "Codex" — barely dips
  - 2023: "GPT-4" — steep plunge begins
  - 2023.5: "Claude" — plunge continues
  - 2024: "Gemini" — plunge accelerates
- **Crossing point (late):** Where blue "Generate" line crosses below dashed "Total Cost" line (~2025), highlighted with a white pulsing circle and label "We are here."

### Animation Sequence
1. **Frame 0–30 (0–1s):** Axes draw on. Title "The Economics of Code" fades in top-left.
2. **Frame 30–120 (1–4s):** All three lines draw from 2015 to ~2020 simultaneously. Blue line is flat and high. Both amber lines are visible. Debt shading fills in real-time. Synced with "For decades, generating new code was expensive..."
3. **Frame 120–210 (4–7s):** Lines continue to 2022. Codex marker appears on blue line. Solid amber starts dropping slightly. Synced with "So when something broke, you patched..."
4. **Frame 210–360 (7–12s):** Solid amber line gets visual emphasis (glow effect). Drops noticeably. Synced with "AI made patching faster too... each patch is getting faster. That's real."
5. **Frame 360–480 (12–16s):** Camera pull-back effect (subtle zoom out ~5%). Debt shading EXPANDS upward as the gap widens. Dashed line stays flat. Synced with "But watch the dashed line. The total cost. It's barely moving."
6. **Frame 480–600 (16–20s):** Blue "Generate" line plunges dramatically from 2023 onward. GPT-4, Claude, Gemini markers appear in sequence. Synced with background narration about generation costs falling.
7. **Frame 600–900 (20–30s):** Hold with ambient animation. Debt area pulses subtly. The visual contrast between the falling solid line and flat dashed line is the key tension.
8. **Frame 900–1050 (30–35s):** Blue line crosses below dashed line. "We are here." label appears. Then blue crosses below even the solid line.
9. **Frame 1050–1380 (35–46s):** Final state holds. All annotations visible. Slow ambient pulse on debt area.

### Typography
- Chart title: Inter SemiBold, 28px, #FFFFFF
- Line labels: Inter Medium, 16px, matching line colors
- AI milestones: Inter Regular, 13px, #8B9DC3, with 1px connecting line to data point
- "We are here." label: Inter Bold, 20px, #FFFFFF, with arrow pointing to crossing
- Y-axis / X-axis labels: Inter Regular, 13px, #8B9DC3

### Easing
- Line draw-on: `easeInOutCubic`
- Blue line plunge (2023+): `easeInQuad` (accelerating drop)
- Debt area expansion: `easeOutCubic`
- Milestone fade-in: `easeOutQuad`
- Zoom-out pull-back: `easeInOutCubic`

## Narration Sync
> "Now look at code."

> "For decades, generating new code was expensive. Writing from scratch took hours, days, weeks. So when something broke, you patched. Of course you patched. It was rational."

> "But something else happened. AI made patching faster too. Cursor, Claude Code, Copilot — you know these tools."

> "Look — each patch is getting faster. That's real. That's what you feel when you use these tools."

> "But watch the dashed line. The total cost. It's barely moving."

> "Because even though each patch is faster, every patch still leaves residue. Technical debt. And that debt accumulates — faster now, because you're patching faster."

Segments: `part1_economics_008` (43.52s – 48.46s) through `part1_economics_013` (78.30s – 89.06s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1380}>
  <AbsoluteFill style={{ backgroundColor: '#0F1923' }}>
    <AnimatedAxes
      xRange={[2015, 2026]}
      yRange={[0, 40]}
      yLabel="Cost (Developer Hours)"
    />
    <AnimatedLine
      data={generateCostData}
      color="#4A90D9"
      strokeWidth={3}
      style="solid"
    />
    <AnimatedLine
      data={immediatePatchData}
      color="#D9944A"
      strokeWidth={3}
      style="solid"
    />
    <AnimatedLine
      data={totalCostWithDebtData}
      color="#D9944A"
      strokeWidth={3}
      style="dashed"
    />
    <ShadedDebtArea
      topLine={totalCostWithDebtData}
      bottomLine={immediatePatchData}
      color="#D9944A"
      opacity={0.1}
    />
    <Sequence from={120}>
      <MilestoneMarker year={2021} label="Codex" />
    </Sequence>
    <Sequence from={480}>
      <MilestoneMarker year={2023} label="GPT-4" />
      <MilestoneMarker year={2023.5} label="Claude" />
      <MilestoneMarker year={2024} label="Gemini" />
    </Sequence>
    <Sequence from={900}>
      <CrossingPointLabel text="We are here." />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "generateCost": [
    { "year": 2015, "hours": 35 },
    { "year": 2018, "hours": 34 },
    { "year": 2021, "hours": 32 },
    { "year": 2022, "hours": 30 },
    { "year": 2023, "hours": 20 },
    { "year": 2024, "hours": 8 },
    { "year": 2025, "hours": 4 },
    { "year": 2026, "hours": 2 }
  ],
  "immediatePatchCost": [
    { "year": 2015, "hours": 8 },
    { "year": 2018, "hours": 7.5 },
    { "year": 2021, "hours": 6 },
    { "year": 2022, "hours": 5 },
    { "year": 2023, "hours": 4.5 },
    { "year": 2024, "hours": 3.5 },
    { "year": 2025, "hours": 3 },
    { "year": 2026, "hours": 2.5 }
  ],
  "totalCostWithDebt": [
    { "year": 2015, "hours": 25 },
    { "year": 2018, "hours": 24 },
    { "year": 2021, "hours": 24 },
    { "year": 2022, "hours": 23.5 },
    { "year": 2023, "hours": 23 },
    { "year": 2024, "hours": 23 },
    { "year": 2025, "hours": 22.5 },
    { "year": 2026, "hours": 22 }
  ],
  "milestones": [
    { "year": 2021, "label": "Codex" },
    { "year": 2023, "label": "GPT-4" },
    { "year": 2023.5, "label": "Claude" },
    { "year": 2024, "label": "Gemini" }
  ]
}
```
