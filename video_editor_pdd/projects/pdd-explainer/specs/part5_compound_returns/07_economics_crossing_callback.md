[Remotion]

# Section 5.7: Economics Crossing Callback — The Chart Returns

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 22:02 - 22:12

## Visual Description
The economics chart from Part 1 returns — but now the viewer sees it with new eyes. The original crossing-point chart (labor cost vs. garment cost) re-enters, and the crossing point pulses with emphasis. Then the chart morphs: the "sock economics" labels transform into "code economics" labels, and the crossing point shifts to "now." The narration delivers the thesis: "When economics change, behavior that was rational becomes... darning socks." The word "darning socks" lingers on screen with a wry visual treatment. This callback creates the full-circle narrative closure that connects the opening metaphor to the technical argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.06)`, 5 evenly spaced

### Chart/Visual Elements
- **Chart Area:** 1200px wide x 500px tall, centered (left margin 360px, top margin 220px)
- **Phase 1 — Sock Chart (reuse from Section 1.2):**
  - X-Axis: Years 1950–2020
  - Labor Cost Line: `#D9944A`, 3px stroke
  - Garment Cost Line: `#4A90D9`, 3px stroke
  - Crossing Point: Glowing circle at ~1962, `#FFFFFF` at 0.8 opacity, glow `rgba(255,255,255,0.3)`
  - Label: "The Threshold"
- **Phase 2 — Morph to Code Chart:**
  - X-Axis morphs: "1950-2020" → "2018-2026"
  - Labels morph: "Labor Cost" → "Total Cost (patching)" | "Garment Cost" → "Generation Cost"
  - Crossing point slides rightward and relabels: "The Threshold" → "Now"
  - "Now" label: `#FFFFFF`, 24px bold, with vertical dashed line extending full chart height, `rgba(255,255,255,0.3)`, animated pulse
- **Thesis Text (Y=800):** "But the economics changed." — `#FFFFFF`, 22px
- **Punchline Text (Y=860):** "And when economics change, behavior that was rational becomes..." — `#FFFFFF` at 0.7 opacity, 18px
- **Final Word (Y=860, inline):** "darning socks." — `#D9944A`, 20px italic, with a subtle strikethrough-style darning needle icon (horizontal line through text, `#D9944A` at 0.4 opacity)

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Sock economics chart fades in (the complete chart from Part 1, already drawn). The viewer recognizes it immediately
2. **Frame 40-70 (1.33-2.33s):** Crossing point pulses — circle scales 1.0→1.3→1.0, glow intensifies then fades. "The Threshold" label brightens
3. **Frame 70-150 (2.33-5.0s):** Chart morphs — this is the key animation beat:
   - X-axis labels cross-fade: year numbers shift from sock era to code era
   - Line labels cross-fade: "Labor Cost" → "Total Cost (patching)", "Garment Cost" → "Generation Cost"
   - Crossing point slides rightward along the X-axis to "2024" position
   - "The Threshold" label morphs to "Now"
   - Vertical dashed line appears at the "Now" position
4. **Frame 150-200 (5.0-6.67s):** "Now" label pulses. Vertical line begins subtle breathing animation (opacity 0.2→0.4→0.2, looping)
5. **Frame 200-250 (6.67-8.33s):** Thesis text fades in at Y=800: "But the economics changed."
6. **Frame 250-280 (8.33-9.33s):** Punchline text fades in: "And when economics change, behavior that was rational becomes..."
7. **Frame 270-290 (9.0-9.67s):** "darning socks." appears in amber italic with the needle icon drawing through it
8. **Frame 290-300 (9.67-10.0s):** Hold. The chart with "Now" marker and the punchline text coexist on screen

### Typography
- Axis Labels: Inter, 16px, regular (400), `#FFFFFF`, opacity 0.5
- "Now" Label: Inter, 24px, bold (700), `#FFFFFF`
- Thesis Text: Inter, 22px, semi-bold (600), `#FFFFFF`
- Punchline Text: Inter, 18px, regular (400), `#FFFFFF` at 0.7 opacity
- "darning socks." Text: Inter, 20px, italic, `#D9944A`

### Easing
- Chart fade-in: `easeOut(quad)`
- Crossing pulse: `easeInOut(sine)`
- Morph transitions: `easeInOut(cubic)` (smooth cross-fades)
- Crossing point slide: `easeInOut(cubic)`
- "Now" pulse: `easeInOut(sine)` (looping)
- Text fades: `easeOut(quad)`

## Narration Sync
> "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Callback Chart (Phase 1) */}
  <Sequence from={0} durationInFrames={70}>
    <SockEconomicsChart
      data={sockChartData}
      crossingHighlight={true}
    />
  </Sequence>

  {/* Morph to Code Chart (Phase 2) */}
  <Sequence from={70} durationInFrames={80}>
    <ChartMorph
      from={{
        xLabels: sockYears,
        lineLabels: ["Labor Cost", "Garment Cost"],
        crossingLabel: "The Threshold",
        crossingX: 1962
      }}
      to={{
        xLabels: codeYears,
        lineLabels: ["Total Cost (patching)", "Generation Cost"],
        crossingLabel: "Now",
        crossingX: 2024
      }}
    />
  </Sequence>

  {/* Now Marker */}
  <Sequence from={150} durationInFrames={50}>
    <NowMarker x={2024} label="Now" pulseColor="#FFFFFF" />
  </Sequence>

  {/* Thesis */}
  <Sequence from={200} durationInFrames={50}>
    <FadeText text="But the economics changed." fontSize={22} y={800} />
  </Sequence>

  {/* Punchline */}
  <Sequence from={250} durationInFrames={50}>
    <FadeText
      text='And when economics change, behavior that was rational becomes...'
      fontSize={18}
      opacity={0.7}
      y={860}
    />
    <Sequence from={20}>
      <StyledText text="darning socks." color="#D9944A" italic={true} fontSize={20} />
      <NeedleIcon through={true} color="#D9944A" opacity={0.4} />
    </Sequence>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chartArea": {
    "width": 1200,
    "height": 500,
    "marginLeft": 360,
    "marginTop": 220
  },
  "phase1": {
    "xAxis": { "label": "Year", "range": [1950, 2020] },
    "lines": [
      { "label": "Labor Cost", "color": "#D9944A" },
      { "label": "Garment Cost", "color": "#4A90D9" }
    ],
    "crossingPoint": { "x": 1962, "y": 45, "label": "The Threshold" }
  },
  "phase2": {
    "xAxis": { "label": "Year", "range": [2018, 2026] },
    "lines": [
      { "label": "Total Cost (patching)", "color": "#D9944A" },
      { "label": "Generation Cost", "color": "#4A90D9" }
    ],
    "crossingPoint": { "x": 2024, "label": "Now" }
  },
  "thesis": "But the economics changed.",
  "punchline": "And when economics change, behavior that was rational becomes...",
  "finalWord": { "text": "darning socks.", "color": "#D9944A" }
}
```

---
