[Remotion]

# Section 3.17: Component Table — What / How / Correctness

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 5:33 - 5:43

## Visual Description

A clean table materializes on screen, presenting the three PDD components in a structured format:

| Component | Encodes | Owner |
|-----------|---------|-------|
| Prompt | WHAT (intent) | Developer |
| Grounding | HOW (style) | Automatic |
| Tests | CORRECTNESS | Accumulated |

The table appears row by row, with each row's color matching its component (amber for Prompt, teal for Grounding, blue for Tests). The table is centered on screen with generous whitespace.

Below the table, a single pulsing line appears: "When these conflict, tests win. Always." This is the hierarchy rule — the walls override everything. The line pulses with blue (test color) emphasis, reinforcing that correctness trumps intent and style.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Table
- Width: 800px, centered at (960, 400)
- Header row: `#1E1E2E` fill, bottom border `#334155` 2px
- Data rows: `#0F172A` fill, bottom border `#1E293B` 1px
- Cell padding: 16px vertical, 24px horizontal
- Column widths: 200px / 300px / 200px

#### Header Text
- "Component" / "Encodes" / "Owner" — Inter, 14px, semi-bold (600), `#64748B`, uppercase, letter-spacing 2px

#### Row Text
- Component names: Inter, 16px, bold (700), color-coded:
  - "Prompt" — `#D9944A`
  - "Grounding" — `#4AD9A0`
  - "Tests" — `#4A90D9`
- Encodes column: Inter, 16px, regular (400), `#E2E8F0`
  - "(intent)" / "(style)" parenthetical: Inter, 14px, `#94A3B8`
- Owner column: Inter, 16px, regular (400), `#CDD6F4`

#### Row Color Accents
- Left border on each row: 3px, matching component color
- "Prompt" row: `#D9944A` left accent
- "Grounding" row: `#4AD9A0` left accent
- "Tests" row: `#4A90D9` left accent

#### Hierarchy Line
- "When these conflict, tests win. Always." — Inter, 18px, semi-bold (600), `#E2E8F0`
- "tests win" highlighted: bold (700), `#4A90D9`
- "Always" highlighted: bold (700), `#4A90D9`
- Positioned below table at y: 620, centered
- Pulse: glow `#4A90D9` at 0.15, 10px blur, cycling

#### Hierarchy Subtext
- "The walls override the specification. The specification overrides the style." — Inter, 14px, regular (400), `#94A3B8`
- Position: y: 660, centered

### Animation Sequence
1. **Frame 0-30 (0-1s):** Table header row fades in with column labels.
2. **Frame 30-60 (1-2s):** Row 1 (Prompt) slides in from left. Amber accent border.
3. **Frame 60-90 (2-3s):** Row 2 (Grounding) slides in from left. Teal accent border.
4. **Frame 90-120 (3-4s):** Row 3 (Tests) slides in from left. Blue accent border. Brief emphasis glow on this row.
5. **Frame 120-180 (4-6s):** Hold on complete table.
6. **Frame 180-240 (6-8s):** Hierarchy line fades in below: "When these conflict, tests win. Always." "tests win" and "Always" pulse blue.
7. **Frame 240-270 (8-9s):** Subtext fades in.
8. **Frame 270-300 (9-10s):** Hold. Table complete, hierarchy established.

### Typography
- Headers: Inter, 14px, semi-bold (600), `#64748B`, uppercase, tracking 2px
- Component names: Inter, 16px, bold (700), color-coded
- Values: Inter, 16px, regular (400), `#E2E8F0`
- Parenthetical: Inter, 14px, `#94A3B8`
- Hierarchy line: Inter, 18px, semi-bold (600), `#E2E8F0`
- Hierarchy emphasis: Inter, 18px, bold (700), `#4A90D9`
- Subtext: Inter, 14px, regular (400), `#94A3B8`

### Easing
- Header fade: `easeOut(quad)` over 15 frames
- Row slide-in: `easeOut(cubic)` over 20 frames each
- Tests row glow: `easeOut(quad)` over 10 frames
- Hierarchy line fade: `easeOut(quad)` over 20 frames
- Pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "When these conflict, tests win. Always. The walls override the specification. The specification overrides the style."

Segment: `part3_mold_parts_021`

- **332.78s** (seg 021): Table begins building
- **335.0s**: Rows appearing
- **338.0s**: "When these conflict, tests win. Always." — hierarchy line appears
- **340.0s**: "The walls override the specification" — subtext
- **342.82s** (seg 021 ends): Hold on complete table with hierarchy

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Table header */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <TableHeader
          columns={["COMPONENT", "ENCODES", "OWNER"]}
          widths={[200, 300, 200]}
          font="Inter" size={14} weight={600}
          color="#64748B" letterSpacing={2}
          y={280}
        />
      </FadeIn>
    </Sequence>

    {/* Table rows */}
    {TABLE_ROWS.map((row, i) => (
      <Sequence key={i} from={30 + i * 30}>
        <SlideIn from="left" distance={40} duration={20}>
          <TableRow
            cells={[row.component, row.encodes, row.owner]}
            accentColor={row.color}
            y={330 + i * 60}
          />
        </SlideIn>
      </Sequence>
    ))}

    {/* Hierarchy line */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <HighlightedText
          text="When these conflict, tests win. Always."
          highlights={[
            { phrase: "tests win", color: "#4A90D9", bold: true },
            { phrase: "Always", color: "#4A90D9", bold: true }
          ]}
          font="Inter" size={18} weight={600} color="#E2E8F0"
          x={960} y={620} align="center"
          pulse={{ color: "#4A90D9", blur: 10, opacity: 0.15, cycleFrames: 30 }}
        />
      </FadeIn>
    </Sequence>

    {/* Subtext */}
    <Sequence from={240}>
      <FadeIn duration={20}>
        <Text text="The walls override the specification. The specification overrides the style."
          font="Inter" size={14} color="#94A3B8"
          x={960} y={660} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "component_table",
  "rows": [
    { "component": "Prompt", "encodes": "WHAT (intent)", "owner": "Developer", "color": "#D9944A" },
    { "component": "Grounding", "encodes": "HOW (style)", "owner": "Automatic", "color": "#4AD9A0" },
    { "component": "Tests", "encodes": "CORRECTNESS", "owner": "Accumulated", "color": "#4A90D9" }
  ],
  "hierarchyRule": "When these conflict, tests win. Always.",
  "hierarchyOrder": ["Tests", "Prompt", "Grounding"],
  "narrationSegments": ["part3_mold_parts_021"],
  "durationSeconds": 10.0
}
```

---
