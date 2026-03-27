[Remotion]

# Section 5.5: Investment Comparison Table — Patching vs. PDD

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 1:06 - 1:15

## Visual Description

A clean, animated comparison table materializes, showing how each investment compounds differently under patching vs. PDD:

| Investment | Patching | PDD |
|------------|----------|-----|
| Fix a bug | One place, once | Impossible forever |
| Improve code | One version | All future versions |
| Document intent | One snapshot | Living specification |

The table uses the 3B1B aesthetic — dark background, minimal borders, clean typography. Each row animates in sequentially. The "Patching" column values appear in amber (`#D9944A`) — limited, singular. The "PDD" column values appear in green (`#5AAA6E`) — expansive, permanent. The contrast in language ("once" vs. "forever", "one version" vs. "all future versions") carries the argument.

A subtle glow sweeps across the PDD column after all rows are visible, reinforcing that this side compounds in your favor.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid — clean table layout

### Chart/Visual Elements

#### Table Layout
- Table width: 1200px, centered at x: 960
- Table top: y: 280
- Row height: 80px
- Column widths: Investment (360px), Patching (360px), PDD (360px)
- Borders: `#334155` at 0.3, 1px — horizontal separators only (no vertical lines)

#### Header Row
- "Investment" — Inter, 16px, semi-bold (600), `#64748B`, uppercase, letter-spacing 2px
- "Patching" — Inter, 16px, semi-bold (600), `#D9944A` at 0.7, uppercase, letter-spacing 2px
- "PDD" — Inter, 16px, semi-bold (600), `#5AAA6E` at 0.7, uppercase, letter-spacing 2px
- Header underline: 2px, `#334155` at 0.5

#### Data Rows
- Investment column: Inter, 18px, regular (400), `#E2E8F0`
- Patching column: Inter, 18px, regular (400), `#D9944A` at 0.8
- PDD column: Inter, 18px, semi-bold (600), `#5AAA6E`

#### Row 1: "Fix a bug" | "One place, once" | "Impossible forever"
#### Row 2: "Improve code" | "One version" | "All future versions"
#### Row 3: "Document intent" | "One snapshot" | "Living specification"

#### PDD Column Glow Sweep
- Linear gradient sweep left-to-right across PDD column: `#5AAA6E` at 0.08, 120px wide

### Animation Sequence
1. **Frame 0-30 (0-1s):** Table header row fades in. Column labels appear. Header underline draws.
2. **Frame 30-70 (1-2.33s):** Row 1 slides in from left. "Fix a bug" → "One place, once" (amber) → "Impossible forever" (green, slight emphasis scale).
3. **Frame 70-110 (2.33-3.67s):** Row 2 slides in. "Improve code" → "One version" → "All future versions".
4. **Frame 110-150 (3.67-5s):** Row 3 slides in. "Document intent" → "One snapshot" → "Living specification".
5. **Frame 150-190 (5-6.33s):** Glow sweep across PDD column, top to bottom.
6. **Frame 190-270 (6.33-9s):** Hold. Table fully visible.

### Typography
- Headers: Inter, 16px, semi-bold (600), respective colors, uppercase, letter-spacing 2px
- Investment labels: Inter, 18px, regular (400), `#E2E8F0`
- Patching values: Inter, 18px, regular (400), `#D9944A` at 0.8
- PDD values: Inter, 18px, semi-bold (600), `#5AAA6E`

### Easing
- Header fade-in: `easeOut(quad)` over 20 frames
- Row slide-in: `easeOut(cubic)` — 15px left slide, 25 frames
- PDD emphasis scale: `easeOut(back)` 1.02 → 1.0
- Glow sweep: `linear` over 40 frames

## Narration Sync
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

Segment: `part5_compound_returns_004`

- **66.06s** (seg 004): Table header appears — "One side of this equation..."
- **68.00s**: Row 1 — "Fix a bug"
- **70.00s**: Row 2 — "Improve code"
- **72.00s**: Row 3 — "Document intent"
- **73.00s**: Glow sweep — "That's not a marginal difference"
- **74.88s** (seg 004 ends): Table fully visible — "Over time, it's everything"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Table header */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <TableHeader
          columns={["INVESTMENT", "PATCHING", "PDD"]}
          colors={["#64748B", "#D9944A", "#5AAA6E"]}
          font="Inter" size={16} weight={600}
          letterSpacing={2} y={280}
        />
        <DrawLine from={[360, 310]} to={[1560, 310]}
          color="#334155" opacity={0.5} width={2}
          drawDuration={15} />
      </FadeIn>
    </Sequence>

    {/* Row 1 */}
    <Sequence from={30}>
      <SlideIn direction="left" distance={15} duration={25}>
        <TableRow y={360}
          cells={[
            { text: "Fix a bug", color: "#E2E8F0" },
            { text: "One place, once", color: "#D9944A", opacity: 0.8 },
            { text: "Impossible forever", color: "#5AAA6E", weight: 600 }
          ]}
        />
      </SlideIn>
    </Sequence>

    {/* Row 2 */}
    <Sequence from={70}>
      <SlideIn direction="left" distance={15} duration={25}>
        <TableRow y={440}
          cells={[
            { text: "Improve code", color: "#E2E8F0" },
            { text: "One version", color: "#D9944A", opacity: 0.8 },
            { text: "All future versions", color: "#5AAA6E", weight: 600 }
          ]}
        />
      </SlideIn>
    </Sequence>

    {/* Row 3 */}
    <Sequence from={110}>
      <SlideIn direction="left" distance={15} duration={25}>
        <TableRow y={520}
          cells={[
            { text: "Document intent", color: "#E2E8F0" },
            { text: "One snapshot", color: "#D9944A", opacity: 0.8 },
            { text: "Living specification", color: "#5AAA6E", weight: 600 }
          ]}
        />
      </SlideIn>
    </Sequence>

    {/* PDD column glow sweep */}
    <Sequence from={150}>
      <GlowSweep
        region={{ x: 1080, y: 280, width: 360, height: 300 }}
        color="#5AAA6E" opacity={0.08}
        sweepWidth={120} duration={40}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_table",
  "chartId": "investment_patching_vs_pdd",
  "columns": ["Investment", "Patching", "PDD"],
  "columnColors": ["#E2E8F0", "#D9944A", "#5AAA6E"],
  "rows": [
    {
      "investment": "Fix a bug",
      "patching": "One place, once",
      "pdd": "Impossible forever"
    },
    {
      "investment": "Improve code",
      "patching": "One version",
      "pdd": "All future versions"
    },
    {
      "investment": "Document intent",
      "patching": "One snapshot",
      "pdd": "Living specification"
    }
  ],
  "narrationSegments": ["part5_compound_returns_004"]
}
```

---
