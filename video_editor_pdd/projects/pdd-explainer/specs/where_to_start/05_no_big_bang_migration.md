[Remotion]

# Section 6.5: No Big Bang — Gradual Migration Bar Chart

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 22:52 - 23:00

## Visual Description
A horizontal stacked bar chart showing a codebase gradually migrating from hand-written code to prompt-driven specification over time. Three time slices are stacked vertically: "Month 1," "Month 3," "Month 6." Each bar has two segments — amber for "Hand-Written Code" and blue for "Prompt-Driven Modules." In Month 1 the bar is 95% amber / 5% blue. By Month 3 it's 60/40. By Month 6 it's 20/80. The bars animate in sequence, making the gradual shift tangible. A crossed-out explosion icon at top-left reinforces "No big bang" — this is incremental. The visual counters the common objection that PDD requires a full rewrite.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Subtle vertical lines at 25%, 50%, 75% marks — `rgba(255,255,255,0.04)`

### Chart/Visual Elements
- **Title:** "Gradual Migration" — `#FFFFFF` at 0.9 opacity, 28px, Inter Bold, top-center at (960, 80)
- **Crossed-Out Explosion Icon:** Top-left at (140, 80)
  - Explosion starburst: `#EF4444` at 0.3 opacity, 40px
  - Red diagonal strikethrough line: `#EF4444` at 0.5 opacity, 2px
  - Label: "No rewrite" — `#EF4444` at 0.4 opacity, 14px, Inter, below icon
- **Bar Chart Area:** Centered, 1000px wide, starting at Y=200
- **Row 1 — Month 1 (Y=220):**
  - Row label: "Month 1" — `#94A3B8`, 16px, Inter, left-aligned at X=340
  - Amber segment: 950px wide (95%), `#D9944A` at 0.7 opacity
  - Blue segment: 50px wide (5%), `#4A90D9` at 0.7 opacity
  - Bar height: 50px, border-radius 4px
- **Row 2 — Month 3 (Y=340):**
  - Row label: "Month 3" — `#94A3B8`, 16px
  - Amber: 600px (60%), Blue: 400px (40%)
- **Row 3 — Month 6 (Y=460):**
  - Row label: "Month 6" — `#94A3B8`, 16px
  - Amber: 200px (20%), Blue: 800px (80%)
- **Legend (Y=600):** Two items side by side, centered
  - Amber square + "Hand-Written Code" — `#D9944A`, 14px
  - Blue square + "Prompt-Driven Modules" — `#4A90D9`, 14px
- **Percentage Labels:** Inside each segment where space allows, `#FFFFFF` at 0.7 opacity, 14px, JetBrains Mono

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** Title fades in. Grid lines draw. Crossed-out explosion icon appears (starburst draws, then strikethrough slashes across it)
2. **Frame 25-80 (0.83-2.67s):** Row 1 animates — row label fades in, then bar grows from left to right. Amber fills first, blue segment pops in at the end. Percentage labels ("95%" / "5%") fade in
3. **Frame 80-135 (2.67-4.5s):** Row 2 animates same pattern. The blue segment is visibly larger now — 40% of the bar
4. **Frame 135-190 (4.5-6.33s):** Row 3 animates. Blue dominates at 80%. The amber segment is small. This is the visual payoff — the gradual shift is clear
5. **Frame 190-210 (6.33-7.0s):** Legend fades in below. A subtle sweep highlight crosses all three blue segments simultaneously (left-to-right, `rgba(74,144,217,0.15)`)
6. **Frame 210-240 (7.0-8.0s):** Hold at final state

### Typography
- Title: Inter, 28px, bold (700), `#FFFFFF` at 0.9 opacity
- Row Labels: Inter, 16px, regular (400), `#94A3B8`
- Percentage Labels: JetBrains Mono, 14px, regular, `#FFFFFF` at 0.7 opacity
- Legend Text: Inter, 14px, regular (400), respective colors
- "No rewrite" Label: Inter, 14px, regular (400), `#EF4444` at 0.4 opacity

### Easing
- Title fade: `easeOut(quad)`
- Bar grow: `easeOut(cubic)`
- Percentage label fade: `easeOut(quad)`
- Explosion strikethrough: `easeInOut(cubic)`
- Legend fade: `easeOut(quad)`
- Sweep highlight: `linear`

## Narration Sync
> "No big bang. No rewrite. Just a gradual migration of where value lives, from code to specification."

Segment: `where_to_start_002` (17.28s – 24.86s)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Title + Icon */}
  <Sequence from={0} durationInFrames={25}>
    <Title text="Gradual Migration" y={80} />
    <CrossedOutExplosion x={140} y={80} />
    <GridLines positions={[0.25, 0.5, 0.75]} />
  </Sequence>

  {/* Row 1: Month 1 */}
  <Sequence from={25} durationInFrames={55}>
    <MigrationBar
      label="Month 1"
      y={220}
      segments={[
        { ratio: 0.95, color: "#D9944A", label: "95%" },
        { ratio: 0.05, color: "#4A90D9", label: "5%" }
      ]}
      totalWidth={1000}
    />
  </Sequence>

  {/* Row 2: Month 3 */}
  <Sequence from={80} durationInFrames={55}>
    <MigrationBar
      label="Month 3"
      y={340}
      segments={[
        { ratio: 0.60, color: "#D9944A", label: "60%" },
        { ratio: 0.40, color: "#4A90D9", label: "40%" }
      ]}
      totalWidth={1000}
    />
  </Sequence>

  {/* Row 3: Month 6 */}
  <Sequence from={135} durationInFrames={55}>
    <MigrationBar
      label="Month 6"
      y={460}
      segments={[
        { ratio: 0.20, color: "#D9944A", label: "20%" },
        { ratio: 0.80, color: "#4A90D9", label: "80%" }
      ]}
      totalWidth={1000}
    />
  </Sequence>

  {/* Legend */}
  <Sequence from={190} durationInFrames={20}>
    <Legend
      items={[
        { color: "#D9944A", label: "Hand-Written Code" },
        { color: "#4A90D9", label: "Prompt-Driven Modules" }
      ]}
      y={600}
    />
    <SweepHighlight color="rgba(74,144,217,0.15)" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "chart": {
    "totalWidth": 1000,
    "barHeight": 50,
    "borderRadius": 4
  },
  "rows": [
    {
      "label": "Month 1",
      "y": 220,
      "segments": [
        { "label": "Hand-Written Code", "ratio": 0.95, "color": "#D9944A" },
        { "label": "Prompt-Driven", "ratio": 0.05, "color": "#4A90D9" }
      ]
    },
    {
      "label": "Month 3",
      "y": 340,
      "segments": [
        { "label": "Hand-Written Code", "ratio": 0.60, "color": "#D9944A" },
        { "label": "Prompt-Driven", "ratio": 0.40, "color": "#4A90D9" }
      ]
    },
    {
      "label": "Month 6",
      "y": 460,
      "segments": [
        { "label": "Hand-Written Code", "ratio": 0.20, "color": "#D9944A" },
        { "label": "Prompt-Driven", "ratio": 0.80, "color": "#4A90D9" }
      ]
    }
  ],
  "legend": [
    { "color": "#D9944A", "label": "Hand-Written Code" },
    { "color": "#4A90D9", "label": "Prompt-Driven Modules" }
  ]
}
```

---
