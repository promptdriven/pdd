[Remotion]

# Section 3.18: Three Components Table — Priority Hierarchy

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 5:30 - 5:44

## Visual Description

A clean, elegant table materializes on screen showing the three mold components, what they encode, and who owns them. The table has three rows and three columns, each row color-coded to its component:

| Component | Encodes | Owner |
|-----------|---------|-------|
| **Prompt** (teal) | WHAT (intent) | Developer |
| **Grounding** (purple) | HOW (style) | Automatic |
| **Tests** (amber) | CORRECTNESS | Accumulated |

Below the table, a single line pulses with emphasis: "When these conflict, tests win. Always." The amber (tests) row briefly glows brighter to reinforce the hierarchy: Tests > Prompt > Grounding.

The code output fades away (it's just output), but the mold — the combination of all three components — continues to glow. This is the closing visual beat of Part 3.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Table
- Position: centered at (960, 400), total width 700px, total height 240px
- Header row: 50px height, bg `#1E293B`, border-bottom `#334155` at 0.3
  - "Component" — Inter, 13px, semi-bold, `#94A3B8`
  - "Encodes" — Inter, 13px, semi-bold, `#94A3B8`
  - "Owner" — Inter, 13px, semi-bold, `#94A3B8`
- Row 1 (Prompt): 60px height, left accent `#2DD4BF` 3px
  - "Prompt" — Inter, 16px, bold, `#2DD4BF`
  - "WHAT (intent)" — Inter, 14px, `#E2E8F0` at 0.7
  - "Developer" — Inter, 14px, `#94A3B8` at 0.6
- Row 2 (Grounding): 60px height, left accent `#A78BFA` 3px
  - "Grounding" — Inter, 16px, bold, `#A78BFA`
  - "HOW (style)" — Inter, 14px, `#E2E8F0` at 0.7
  - "Automatic" — Inter, 14px, `#94A3B8` at 0.6
- Row 3 (Tests): 60px height, left accent `#D9944A` 3px
  - "Tests" — Inter, 16px, bold, `#D9944A`
  - "CORRECTNESS" — Inter, 14px, `#E2E8F0` at 0.7
  - "Accumulated" — Inter, 14px, `#94A3B8` at 0.6

#### Priority Line
- Position: centered at (960, 680)
- "When these conflict, tests win. Always." — Inter, 20px, bold, `#D9944A` at 0.8
- Subtle amber glow pulse, 15px radius

#### Priority Arrows (below table)
- Small downward hierarchy: Tests → Prompt → Grounding
- "overrides" labels between, Inter, 10px, `#64748B` at 0.3

#### Code Output Fade
- Small code block at bottom right, `#64748B` at 0.2
- Fades away — "The code is output."
- Mold icon at bottom left, all three colors, continues to glow
- "The mold is what matters." — Inter, 14px, `#E2E8F0` at 0.5

### Animation Sequence
1. **Frame 0-30 (0-1s):** Table header row appears.
2. **Frame 30-90 (1-3s):** Row 1 (Prompt) slides in from left with teal accent.
3. **Frame 90-150 (3-5s):** Row 2 (Grounding) slides in with purple accent.
4. **Frame 150-210 (5-7s):** Row 3 (Tests) slides in with amber accent.
5. **Frame 210-300 (7-10s):** Priority line appears below: "When these conflict, tests win. Always." Tests row glows brighter.
6. **Frame 300-360 (10-12s):** Priority arrows appear showing hierarchy.
7. **Frame 360-420 (12-14s):** Code output fades at bottom right. Mold icon glows at bottom left. "The mold is what matters."

### Typography
- Header: Inter, 13px, semi-bold (600), `#94A3B8`
- Component names: Inter, 16px, bold (700), respective colors
- Encodes/Owner: Inter, 14px, `#E2E8F0` at 0.7 / `#94A3B8` at 0.6
- Priority line: Inter, 20px, bold (700), `#D9944A` at 0.8
- Priority arrows: Inter, 10px, `#64748B` at 0.3

### Easing
- Header appear: `easeOut(quad)` over 15 frames
- Row slide-in: `easeOut(cubic)` over 20 frames, 15px from left
- Priority line: `easeOut(quad)` over 20 frames
- Tests glow: `easeOut(cubic)` over 30 frames, then `easeInOut(sine)` pulse
- Code fade: `easeIn(quad)` over 30 frames
- Mold glow: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."
> "The code is output. The mold is what matters."

Segments: `part3_mold_three_parts_029`, `part3_mold_three_parts_030`

- **5:30** ("When these conflict"): Table materializes, priority line appears
- **5:38** ("walls override"): Tests row glows, hierarchy arrows visible
- **5:41** ("code is output"): Code fades, mold glows

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Table */}
    <DataTable x={960} y={400} width={700} height={240}>
      {/* Header */}
      <Sequence from={0}>
        <FadeIn duration={15}>
          <TableHeader columns={["Component", "Encodes", "Owner"]}
            font="Inter" fontSize={13} weight={600}
            color="#94A3B8" bg="#1E293B" />
        </FadeIn>
      </Sequence>

      {/* Rows */}
      {TABLE_ROWS.map((row, i) => (
        <Sequence from={30 + i * 60} key={row.component}>
          <SlideIn fromX={-15} duration={20}>
            <TableRow
              accent={row.color} accentWidth={3}
              cells={[
                { text: row.component, font: "Inter", size: 16, weight: 700, color: row.color },
                { text: row.encodes, font: "Inter", size: 14, color: "#E2E8F0", opacity: 0.7 },
                { text: row.owner, font: "Inter", size: 14, color: "#94A3B8", opacity: 0.6 }
              ]} />
          </SlideIn>
        </Sequence>
      ))}
    </DataTable>

    {/* Priority line */}
    <Sequence from={210}>
      <FadeIn duration={20}>
        <PulsingText
          text="When these conflict, tests win. Always."
          font="Inter" size={20} weight={700}
          color="#D9944A" opacity={0.8}
          x={960} y={680} align="center"
          pulseCycle={40} glowRadius={15} />
      </FadeIn>
    </Sequence>

    {/* Code output fade + mold glow */}
    <Sequence from={360}>
      <FadeOut duration={30}>
        <MiniCodeBlock x={1400} y={850} opacity={0.2} />
      </FadeOut>
      <MoldIcon x={500} y={850}
        colors={["#2DD4BF", "#A78BFA", "#D9944A"]}
        pulse={40} />
      <FadeIn duration={15}>
        <Text text="The mold is what matters."
          font="Inter" size={14} color="#E2E8F0" opacity={0.5}
          x={960} y={950} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "three_components_table",
  "table": {
    "columns": ["Component", "Encodes", "Owner"],
    "rows": [
      { "component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#2DD4BF" },
      { "component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#A78BFA" },
      { "component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#D9944A" }
    ]
  },
  "priorityRule": "When these conflict, tests win. Always.",
  "hierarchy": ["Tests", "Prompt", "Grounding"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_029", "part3_mold_three_parts_030"]
}
```

---
