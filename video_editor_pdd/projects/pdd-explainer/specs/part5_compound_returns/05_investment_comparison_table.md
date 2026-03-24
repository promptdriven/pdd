[Remotion]

# Section 5.5: Investment Comparison Table — Patching vs PDD

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 1:02 - 1:11

## Visual Description

A clean comparison table appears, row by row, contrasting how the same investment yields different returns under Patching vs PDD. Three rows reveal the systematic advantage:

| Investment | Patching | PDD |
|------------|----------|-----|
| Fix a bug | One place, once | Impossible forever |
| Improve code | One version | All future versions |
| Document intent | One snapshot | Living specification |

The PDD column is highlighted in green — each entry represents a compound return. The Patching column is in muted amber — each entry represents a one-time, depreciating action. The contrast between "one" (temporal, local) and "all/forever" (permanent, global) is the key visual takeaway.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Table Container
- Width: 1200px, centered horizontally
- Position: centered vertically at y=440
- Background: `#0F1729` at 0.6
- Border: 1px `#1E293B`
- Border-radius: 12px
- Padding: 32px

#### Header Row
- Background: `#1A2540` at 0.8
- Columns:
  - "Investment" — Inter, 14px, semi-bold (600), `#94A3B8`
  - "Patching" — Inter, 14px, semi-bold (600), `#F59E0B` at 0.8
  - "PDD" — Inter, 14px, semi-bold (600), `#4ADE80` at 0.8
- Column widths: 30% | 30% | 40%
- Height: 48px
- Bottom border: 1px `#334155`

#### Data Rows (3 rows)
- Row height: 56px
- Bottom border: 1px `#1E293B` at 0.5
- Investment column: Inter, 15px, semi-bold (600), `#E2E8F0` at 0.9
- Patching column: Inter, 15px, regular (400), `#F59E0B` at 0.6
- PDD column: Inter, 15px, semi-bold (600), `#4ADE80` at 0.9

#### Row Data
1. "Fix a bug" | "One place, once" | "Impossible forever"
2. "Improve code" | "One version" | "All future versions"
3. "Document intent" | "One snapshot" | "Living specification"

#### PDD Column Highlight
- Each PDD cell has a faint green left border: 3px `#4ADE80` at 0.3
- On row reveal, PDD cell briefly pulses: background `#4ADE80` at 0.04 → 0.0

### Animation Sequence
1. **Frame 0-30 (0-1s):** Table container fades in. Header row appears. `easeOutQuad`.
2. **Frame 30-90 (1-3s):** Row 1 slides in from right. "Fix a bug" → "One place, once" → "Impossible forever". PDD cell pulses green briefly.
3. **Frame 90-150 (3-5s):** Row 2 slides in. "Improve code" → "One version" → "All future versions". PDD cell pulses.
4. **Frame 150-210 (5-7s):** Row 3 slides in. "Document intent" → "One snapshot" → "Living specification". PDD cell pulses.
5. **Frame 210-270 (7-9s):** Hold. All rows visible. Faint green glow on PDD column.

### Typography
- Header: Inter, 14px, semi-bold (600)
- Investment column: Inter, 15px, semi-bold (600), `#E2E8F0`
- Patching column: Inter, 15px, regular (400), `#F59E0B` at 0.6
- PDD column: Inter, 15px, semi-bold (600), `#4ADE80`

### Easing
- Container fade: `easeOut(quad)` over 20 frames
- Row slide-in: `easeOut(cubic)` over 25 frames
- PDD pulse: `easeOut(quad)` over 15 frames (opacity 0.04 → 0.0)

## Narration Sync
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

Segment: `part5_compound_returns_006`

- **1:02** ("One side of this equation"): Table container and header appear
- **1:04** ("compounds against you"): Row 1 reveals
- **1:06** ("The other compounds for you"): Row 2 reveals
- **1:08** ("marginal difference"): Row 3 reveals
- **1:11** ("it's everything"): Hold — all rows visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Table container */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <TableContainer width={1200} y={440}
          bg="#0F1729" border="#1E293B" radius={12}>

          {/* Header */}
          <TableHeader
            columns={["Investment", "Patching", "PDD"]}
            colors={["#94A3B8", "#F59E0B", "#4ADE80"]}
            bg="#1A2540" />

          {/* Row 1 */}
          <Sequence from={30}>
            <SlideIn direction="right" duration={25}>
              <TableRow
                cells={["Fix a bug", "One place, once", "Impossible forever"]}
                pddHighlight />
            </SlideIn>
          </Sequence>

          {/* Row 2 */}
          <Sequence from={90}>
            <SlideIn direction="right" duration={25}>
              <TableRow
                cells={["Improve code", "One version", "All future versions"]}
                pddHighlight />
            </SlideIn>
          </Sequence>

          {/* Row 3 */}
          <Sequence from={150}>
            <SlideIn direction="right" duration={25}>
              <TableRow
                cells={["Document intent", "One snapshot", "Living specification"]}
                pddHighlight />
            </SlideIn>
          </Sequence>
        </TableContainer>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_table",
  "tableId": "investment_comparison",
  "columns": ["Investment", "Patching", "PDD"],
  "columnColors": ["#E2E8F0", "#F59E0B", "#4ADE80"],
  "rows": [
    { "investment": "Fix a bug", "patching": "One place, once", "pdd": "Impossible forever" },
    { "investment": "Improve code", "patching": "One version", "pdd": "All future versions" },
    { "investment": "Document intent", "patching": "One snapshot", "pdd": "Living specification" }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part5_compound_returns_006"]
}
```

---
