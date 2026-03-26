[Remotion]

# Section 5.5: Investment Comparison Table — Patching vs. PDD Returns

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 1:02 - 1:11

## Visual Description
A clean, structured comparison table appears, reinforcing the diverging curves with concrete examples. The table has three columns — "Investment", "Patching", and "PDD" — and three rows comparing how each approach handles bug fixes, code improvements, and documentation.

The table builds row by row. The "Patching" column entries appear in muted amber, suggesting limitation. The "PDD" column entries appear in bright teal with a subtle glow, suggesting compounding value. Each PDD cell feels like a win.

The table design is minimal and modern — no heavy borders, just horizontal dividers and plenty of whitespace.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines

### Chart/Visual Elements

#### Table Layout
- Table width: `1100px`, centered horizontally
- Table top: `280px` from top
- Column widths: `280px` (Investment), `360px` (Patching), `360px` (PDD)
- Row height: `80px`
- Row dividers: `1px` solid, `#1E293B` opacity `0.4`

#### Header Row
- Background: none (transparent)
- "Investment" — Inter, 14px, bold, `#64748B`, uppercase, letter-spacing `1.5px`
- "Patching" — Inter, 14px, bold, `#D9944A`, uppercase, letter-spacing `1.5px`
- "PDD" — Inter, 14px, bold, `#4A90D9`, uppercase, letter-spacing `1.5px`
- Bottom border: `2px` solid `#334155`

#### Row 1 — Fix a Bug
- Investment: "Fix a bug" — Inter, 16px, medium (500), `#E2E8F0`
- Patching: "One place, once" — Inter, 16px, regular (400), `#D9944A` opacity `0.7`
- PDD: "Impossible forever" — Inter, 16px, bold (600), `#4A90D9`
- PDD cell has subtle left-border accent: `3px` solid `#4A90D9` opacity `0.3`

#### Row 2 — Improve Code
- Investment: "Improve code" — Inter, 16px, medium (500), `#E2E8F0`
- Patching: "One version" — Inter, 16px, regular (400), `#D9944A` opacity `0.7`
- PDD: "All future versions" — Inter, 16px, bold (600), `#4A90D9`
- PDD cell has subtle left-border accent: `3px` solid `#4A90D9` opacity `0.3`

#### Row 3 — Document Intent
- Investment: "Document intent" — Inter, 16px, medium (500), `#E2E8F0`
- Patching: "One snapshot" — Inter, 16px, regular (400), `#D9944A` opacity `0.7`
- PDD: "Living specification" — Inter, 16px, bold (600), `#4A90D9`
- PDD cell has subtle left-border accent: `3px` solid `#4A90D9` opacity `0.3`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Header row fades in. Column titles appear. Bottom border draws left-to-right.
2. **Frame 30-90 (1-3s):** Row 1 slides in from right (translateX `+40px→0`) with fade. All three cells appear simultaneously.
3. **Frame 90-150 (3-5s):** Row 2 slides in with the same animation.
4. **Frame 150-210 (5-7s):** Row 3 slides in.
5. **Frame 210-240 (7-8s):** All PDD cells get a brief simultaneous glow pulse — the left-border accents pulse brightness from `0.3→0.6→0.3`.
6. **Frame 240-300 (8-10s):** Hold. The table sits, clean and persuasive.

### Typography
- Column headers: Inter, 14px, bold (700), respective colors, uppercase, letter-spacing `1.5px`
- Investment column: Inter, 16px, medium (500), `#E2E8F0`
- Patching column: Inter, 16px, regular (400), `#D9944A` opacity `0.7`
- PDD column: Inter, 16px, bold (600), `#4A90D9`

### Easing
- Row slide-in: `easeOutCubic` over 30 frames
- Row fade-in: `easeOutQuad` over 25 frames
- Header border draw: `easeInOutCubic` over 20 frames
- Glow pulse: `easeInOutSine` over 30 frames

## Narration Sync
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Header row */}
    <Sequence from={0}>
      <FadeIn durationInFrames={25}>
        <TableHeader
          columns={["Investment", "Patching", "PDD"]}
          colors={["#64748B", "#D9944A", "#4A90D9"]}
          font="Inter" size={14} weight={700}
          uppercase letterSpacing="1.5px"
          borderColor="#334155" borderWidth={2}
          borderDrawDuration={20} />
      </FadeIn>
    </Sequence>

    {/* Row 1: Fix a bug */}
    <Sequence from={30}>
      <SlideAndFade fromX={40} durationInFrames={30} easing="easeOutCubic">
        <TableRow
          cells={[
            { text: "Fix a bug", color: "#E2E8F0", weight: 500 },
            { text: "One place, once", color: "#D9944A", opacity: 0.7 },
            { text: "Impossible forever", color: "#4A90D9", weight: 600,
              accentBorder: { color: "#4A90D9", opacity: 0.3, width: 3 } }
          ]}
          dividerColor="#1E293B" dividerOpacity={0.4} />
      </SlideAndFade>
    </Sequence>

    {/* Row 2: Improve code */}
    <Sequence from={90}>
      <SlideAndFade fromX={40} durationInFrames={30} easing="easeOutCubic">
        <TableRow
          cells={[
            { text: "Improve code", color: "#E2E8F0", weight: 500 },
            { text: "One version", color: "#D9944A", opacity: 0.7 },
            { text: "All future versions", color: "#4A90D9", weight: 600,
              accentBorder: { color: "#4A90D9", opacity: 0.3, width: 3 } }
          ]}
          dividerColor="#1E293B" dividerOpacity={0.4} />
      </SlideAndFade>
    </Sequence>

    {/* Row 3: Document intent */}
    <Sequence from={150}>
      <SlideAndFade fromX={40} durationInFrames={30} easing="easeOutCubic">
        <TableRow
          cells={[
            { text: "Document intent", color: "#E2E8F0", weight: 500 },
            { text: "One snapshot", color: "#D9944A", opacity: 0.7 },
            { text: "Living specification", color: "#4A90D9", weight: 600,
              accentBorder: { color: "#4A90D9", opacity: 0.3, width: 3 } }
          ]}
          dividerColor="#1E293B" dividerOpacity={0.4} />
      </SlideAndFade>
    </Sequence>

    {/* PDD column glow pulse */}
    <Sequence from={210}>
      <GlowPulse targets="pdd_cells"
        property="accentBorderOpacity"
        from={0.3} to={0.6}
        durationInFrames={30} easing="easeInOutSine" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_table",
  "columns": [
    { "id": "investment", "label": "Investment", "color": "#64748B" },
    { "id": "patching", "label": "Patching", "color": "#D9944A" },
    { "id": "pdd", "label": "PDD", "color": "#4A90D9" }
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
  ],
  "narrationSegments": ["part5_compound_returns_006"]
}
```
