[Remotion]

# Section 5.5: Investment Comparison Table — Patching vs PDD

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 21:38 - 21:52

## Visual Description
A clean data table materializes, making the compound returns argument concrete and actionable. Three rows compare identical investments (fixing a bug, improving code, documenting intent) and show radically different outcomes between Patching and PDD. Each row animates in with a stagger, and the PDD column glows progressively brighter as the pattern becomes clear: every investment in PDD compounds forward. Below the table, a pulsing summary line crystallizes the core thesis: "One side compounds against you. The other compounds for you." This is the table the viewer will screenshot and share.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Table:** Centered at (960, 420), 1000px wide
  - 3 columns: "Investment" (320px), "Patching" (320px), "PDD" (320px)
  - Header row: `#FFFFFF` at 0.6 opacity, 18px bold, underline `rgba(255,255,255,0.1)`
  - Column header "Patching": `#D9944A` at 0.8 opacity
  - Column header "PDD": `#4A90D9` at 0.8 opacity
  - Row dividers: `rgba(255,255,255,0.05)`, 1px
  - Row height: 70px
- **Row 1:**
  - Investment: "Fix a bug" — `#FFFFFF`, 18px
  - Patching: "One place, once" — `#D9944A` at 0.6 opacity, 18px
  - PDD: "Impossible forever" — `#4A90D9`, 18px, with subtle glow `rgba(74,144,217,0.15)`
- **Row 2:**
  - Investment: "Improve code" — `#FFFFFF`, 18px
  - Patching: "One version" — `#D9944A` at 0.6 opacity, 18px
  - PDD: "All future versions" — `#4A90D9`, 18px, with subtle glow `rgba(74,144,217,0.15)`
- **Row 3:**
  - Investment: "Document intent" — `#FFFFFF`, 18px
  - Patching: "One snapshot" — `#D9944A` at 0.6 opacity, 18px
  - PDD: "Living specification" — `#4A90D9`, 18px, with subtle glow `rgba(74,144,217,0.15)`
- **Summary Line (Y=700):** "One side compounds against you. The other compounds for you." — `#FFFFFF`, 22px semi-bold
  - "against you" highlighted in `#D9944A`
  - "for you" highlighted in `#4A90D9`
- **Closing Line (Y=760):** "That's not a marginal difference. Over time, it's everything." — `#FFFFFF` at 0.5 opacity, 16px

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Table header row draws in — column headers fade in left-to-right. Underline draws. "Patching" header in amber, "PDD" header in blue
2. **Frame 40-100 (1.33-3.33s):** Row 1 animates in — Investment cell slides from left (20px drift), then Patching cell fades in, then PDD cell fades in with a brief blue glow pulse. 15-frame stagger between cells
3. **Frame 100-160 (3.33-5.33s):** Row 2 animates in — same pattern, 15-frame cell stagger
4. **Frame 160-220 (5.33-7.33s):** Row 3 animates in — same pattern, 15-frame cell stagger
5. **Frame 220-280 (7.33-9.33s):** PDD column glows — all three PDD cells simultaneously pulse with `rgba(74,144,217,0.2)` backlight, emphasizing the compound pattern. Patching column dims slightly (opacity drops to 0.4)
6. **Frame 280-350 (9.33-11.67s):** Summary line fades in. "against you" word group pulses amber. "for you" word group pulses blue. Both pulses are subtle (opacity 0.7→1.0→0.8)
7. **Frame 350-390 (11.67-13.0s):** Closing line fades in below
8. **Frame 390-420 (13.0-14.0s):** Hold at final state

### Typography
- Column Headers: Inter, 18px, bold (700), respective colors
- Cell Text (Investment): Inter, 18px, medium (500), `#FFFFFF`
- Cell Text (Patching): Inter, 18px, regular (400), `#D9944A` at 0.6 opacity
- Cell Text (PDD): Inter, 18px, regular (400), `#4A90D9`
- Summary Line: Inter, 22px, semi-bold (600), `#FFFFFF` (with color highlights)
- Closing Line: Inter, 16px, regular (400), `#FFFFFF` at 0.5 opacity

### Easing
- Header draw: `easeOut(cubic)`
- Cell slide-in: `easeOut(cubic)`
- Cell fade: `easeOut(quad)`
- PDD glow pulse: `easeInOut(sine)`
- Patching dim: `easeOut(quad)`
- Summary fade: `easeOut(quad)`
- Highlight pulse: `easeInOut(sine)`

## Narration Sync
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  {/* Header */}
  <Sequence from={0} durationInFrames={40}>
    <TableHeader
      columns={[
        { label: "Investment", color: "#FFFFFF" },
        { label: "Patching", color: "#D9944A" },
        { label: "PDD", color: "#4A90D9" }
      ]}
      columnWidths={[320, 320, 320]}
    />
  </Sequence>

  {/* Row 1 */}
  <Sequence from={40} durationInFrames={60}>
    <TableRow
      cells={["Fix a bug", "One place, once", "Impossible forever"]}
      cellColors={["#FFFFFF", "#D9944A", "#4A90D9"]}
      cellStagger={15}
      pddGlow={true}
    />
  </Sequence>

  {/* Row 2 */}
  <Sequence from={100} durationInFrames={60}>
    <TableRow
      cells={["Improve code", "One version", "All future versions"]}
      cellColors={["#FFFFFF", "#D9944A", "#4A90D9"]}
      cellStagger={15}
      pddGlow={true}
    />
  </Sequence>

  {/* Row 3 */}
  <Sequence from={160} durationInFrames={60}>
    <TableRow
      cells={["Document intent", "One snapshot", "Living specification"]}
      cellColors={["#FFFFFF", "#D9944A", "#4A90D9"]}
      cellStagger={15}
      pddGlow={true}
    />
  </Sequence>

  {/* Column Emphasis */}
  <Sequence from={220} durationInFrames={60}>
    <ColumnGlow column="pdd" color="rgba(74,144,217,0.2)" />
    <ColumnDim column="patching" targetOpacity={0.4} />
  </Sequence>

  {/* Summary */}
  <Sequence from={280} durationInFrames={70}>
    <HighlightedText
      text="One side compounds against you. The other compounds for you."
      highlights={[
        { words: "against you", color: "#D9944A" },
        { words: "for you", color: "#4A90D9" }
      ]}
      fontSize={22}
      y={700}
    />
  </Sequence>

  {/* Closing */}
  <Sequence from={350} durationInFrames={40}>
    <FadeText
      text="That's not a marginal difference. Over time, it's everything."
      opacity={0.5}
      y={760}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "table": {
    "width": 1000,
    "center": { "x": 960, "y": 420 },
    "columnWidths": [320, 320, 320],
    "rowHeight": 70,
    "headers": [
      { "label": "Investment", "color": "#FFFFFF" },
      { "label": "Patching", "color": "#D9944A" },
      { "label": "PDD", "color": "#4A90D9" }
    ],
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
    ]
  },
  "summary": {
    "text": "One side compounds against you. The other compounds for you.",
    "highlights": {
      "against you": "#D9944A",
      "for you": "#4A90D9"
    }
  }
}
```

---
