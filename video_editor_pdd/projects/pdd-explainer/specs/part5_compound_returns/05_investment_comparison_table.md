[Remotion]

# Section 5.5: Investment Comparison Table — Compounds For You

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 21:44 - 21:58

## Visual Description

A clean data table materializes, comparing how identical investments play out under patching vs PDD. Three rows appear one by one: "Fix a bug", "Improve code", "Document intent." The Patching column shows limited, single-use outcomes ("One place, once", "One version", "One snapshot"). The PDD column shows compounding, permanent outcomes ("Impossible forever", "All future versions", "Living specification") — and each PDD cell glows progressively brighter as the rows stack up, visualizing the compounding effect.

This is the "screenshot moment" — the cleanest summary of the entire section's argument. Below the table, a summary line appears: "One side compounds against you. The other compounds for you." The PDD column cells pulse once in unison to land the point.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none (clean data presentation)

### Chart/Visual Elements

#### Table Container
- Position: centered at (960, 460)
- Width: 900px, auto-height
- Border: 1px `#334155` at 0.3, rounded 8px
- Background: `#0F172A`

#### Table Header Row
- Height: 50px
- Background: `#1E293B` at 0.4
- Columns:
  - "INVESTMENT" — Inter, 12px, semi-bold (600), `#94A3B8` at 0.5, letter-spacing 2px, left-aligned, 300px wide
  - "PATCHING" — Inter, 12px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, center-aligned, 300px wide
  - "PDD" — Inter, 12px, semi-bold (600), `#4A90D9` at 0.5, letter-spacing 2px, center-aligned, 300px wide

#### Row 1 — Fix a bug
- Height: 70px
- Background: `#0F172A`
- Border-bottom: 1px `#1E293B` at 0.3
- Investment cell: "Fix a bug" — Inter, 16px, `#E2E8F0`, left-aligned with 24px padding
  - Icon: bug glyph, `#94A3B8` at 0.4, before text
- Patching cell: "One place, once" — Inter, 15px, `#D9944A` at 0.6, center-aligned
- PDD cell: "Impossible forever" — Inter, 15px, semi-bold (600), `#4A90D9` at 0.8, center-aligned
  - Glow background: `#4A90D9` at 0.04

#### Row 2 — Improve code
- Height: 70px
- Background: `#111827` at 0.3 (alternating)
- Border-bottom: 1px `#1E293B` at 0.3
- Investment cell: "Improve code" — Inter, 16px, `#E2E8F0`, left-aligned with 24px padding
  - Icon: code arrow glyph, `#94A3B8` at 0.4, before text
- Patching cell: "One version" — Inter, 15px, `#D9944A` at 0.6, center-aligned
- PDD cell: "All future versions" — Inter, 15px, semi-bold (600), `#4A90D9` at 0.9, center-aligned
  - Glow background: `#4A90D9` at 0.06 (brighter than row 1)

#### Row 3 — Document intent
- Height: 70px
- Background: `#0F172A`
- Investment cell: "Document intent" — Inter, 16px, `#E2E8F0`, left-aligned with 24px padding
  - Icon: document glyph, `#94A3B8` at 0.4, before text
- Patching cell: "One snapshot" — Inter, 15px, `#D9944A` at 0.6, center-aligned
- PDD cell: "Living specification" — Inter, 15px, semi-bold (600), `#4A90D9` at 1.0, center-aligned
  - Glow background: `#4A90D9` at 0.08 (brightest)

#### Summary Line
- Position: centered at y: 700
- Text: "One side compounds against you. The other compounds for you."
- Inter, 20px, semi-bold (600), `#E2E8F0`
- "against you" colored `#D9944A`
- "for you" colored `#4A90D9`
- Background pill: `#1E293B` at 0.25, rounded 10px, padding 16px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Table container fades in. Header row appears with column labels.
2. **Frame 30-90 (1-3s):** Row 1 slides in from bottom. Investment cell first, then Patching cell types in, then PDD cell appears with glow.
3. **Frame 90-150 (3-5s):** Row 2 slides in. Same sequence. PDD glow is slightly brighter.
4. **Frame 150-210 (5-7s):** Row 3 slides in. Same sequence. PDD glow is brightest — the progressive brightening is now visible as a pattern.
5. **Frame 210-270 (7-9s):** All three PDD cells pulse together — opacity scales from current to +0.1 and back. The compounding visual pattern lands.
6. **Frame 270-330 (9-11s):** Summary line slides up from bottom: "One side compounds against you. The other compounds for you."
7. **Frame 330-420 (11-14s):** Hold on complete table. This is the screenshot.

### Typography
- Header labels: Inter, 12px, semi-bold (600), respective colors at 0.5, letter-spacing 2px
- Investment text: Inter, 16px, `#E2E8F0`
- Patching values: Inter, 15px, `#D9944A` at 0.6
- PDD values: Inter, 15px, semi-bold (600), `#4A90D9` at 0.8-1.0 (progressive)
- Summary: Inter, 20px, semi-bold (600), `#E2E8F0` with colored keywords

### Easing
- Table container fade: `easeOut(quad)` over 20 frames
- Row slide-in: `easeOut(cubic)` from y+15, 20 frames
- Cell type-in: staggered by 10 frames per column
- PDD glow appear: `easeOut(quad)` over 15 frames
- PDD pulse: `easeInOut(sine)` over 30 frames
- Summary slide-up: `easeOut(cubic)` from y+20, 25 frames

## Narration Sync
> "One side of this equation compounds against you. The other compounds for you. That's not a marginal difference. Over time, it's everything."

Segment: `part5_005`

- **21:44** ("One side of this equation"): Table rows appear with comparison data
- **21:48** ("compounds against you"): Patching column visible, amber emphasis
- **21:50** ("The other compounds for you"): PDD cells pulse together
- **21:54** ("That's not a marginal difference"): Summary line appears
- **21:56** ("Over time, it's everything"): Hold on complete table

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Table container */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <TableContainer
          position={[960, 460]} width={900}
          border={{ color: '#334155', opacity: 0.3, radius: 8 }}>

          {/* Header row */}
          <TableHeader bgColor="#1E293B" bgOpacity={0.4}>
            <HeaderCell text="INVESTMENT" color="#94A3B8" width={300} align="left" />
            <HeaderCell text="PATCHING" color="#D9944A" width={300} align="center" />
            <HeaderCell text="PDD" color="#4A90D9" width={300} align="center" />
          </TableHeader>
        </TableContainer>
      </FadeIn>
    </Sequence>

    {/* Row 1 — Fix a bug */}
    <Sequence from={30}>
      <SlideUp distance={15} duration={20}>
        <TableRow icon="bug" investment="Fix a bug"
          patching="One place, once"
          pdd="Impossible forever"
          pddGlow={0.04} />
      </SlideUp>
    </Sequence>

    {/* Row 2 — Improve code */}
    <Sequence from={90}>
      <SlideUp distance={15} duration={20}>
        <TableRow icon="code_arrow" investment="Improve code"
          patching="One version"
          pdd="All future versions"
          pddGlow={0.06} alternate />
      </SlideUp>
    </Sequence>

    {/* Row 3 — Document intent */}
    <Sequence from={150}>
      <SlideUp distance={15} duration={20}>
        <TableRow icon="document" investment="Document intent"
          patching="One snapshot"
          pdd="Living specification"
          pddGlow={0.08} />
      </SlideUp>
    </Sequence>

    {/* PDD column pulse */}
    <Sequence from={210}>
      <PulseGroup targets={['pdd_cell_1','pdd_cell_2','pdd_cell_3']}
        opacityDelta={0.1} duration={30} />
    </Sequence>

    {/* Summary line */}
    <Sequence from={270}>
      <SlideUp distance={20} duration={25}>
        <PillLabel x={960} y={700}
          bgColor="#1E293B" bgOpacity={0.25} borderRadius={10} padding={16}>
          <RichText font="Inter" size={20} weight={600}>
            <Span color="#E2E8F0">One side compounds </Span>
            <Span color="#D9944A">against you</Span>
            <Span color="#E2E8F0">. The other compounds </Span>
            <Span color="#4A90D9">for you</Span>
            <Span color="#E2E8F0">.</Span>
          </RichText>
        </PillLabel>
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "comparison_table",
  "chartId": "investment_comparison",
  "columns": ["Investment", "Patching", "PDD"],
  "rows": [
    {
      "investment": "Fix a bug",
      "icon": "bug",
      "patching": "One place, once",
      "pdd": "Impossible forever",
      "pddGlowIntensity": 0.04
    },
    {
      "investment": "Improve code",
      "icon": "code_arrow",
      "patching": "One version",
      "pdd": "All future versions",
      "pddGlowIntensity": 0.06
    },
    {
      "investment": "Document intent",
      "icon": "document",
      "patching": "One snapshot",
      "pdd": "Living specification",
      "pddGlowIntensity": 0.08
    }
  ],
  "summary": "One side compounds against you. The other compounds for you.",
  "colors": {
    "patching": "#D9944A",
    "pdd": "#4A90D9",
    "text": "#E2E8F0"
  },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part5_005"]
}
```

---
