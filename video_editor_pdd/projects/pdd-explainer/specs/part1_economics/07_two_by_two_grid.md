[Remotion]

# Section 1.7: Productivity Quadrant — The 2×2 That Explains Everything

**Tool:** Remotion
**Duration:** ~22s (660 frames @ 30fps)
**Timestamp:** 3:26 - 3:48

## Visual Description

A clean 2×2 grid appears, resolving the apparent contradiction between AI productivity studies. X-axis: "Greenfield → Brownfield". Y-axis: "In-Distribution → Out-of-Distribution".

The top-left quadrant (greenfield + in-distribution) glows green with "GitHub study: +55%". The bottom-right quadrant (brownfield + out-of-distribution) glows red with "METR study: −19%". The other two quadrants are intermediate gray. A bottom label reads: "Every study is correct. They just measured different quadrants."

This is the explanatory synthesis — the moment the viewer understands why the studies seem contradictory. The 3B1B aesthetic of clean geometry with precise labeling.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines (the 2×2 IS the grid)

### Chart/Visual Elements

#### 2×2 Grid Structure
- Total size: 640×480px, centered at (960, 480)
- Cell size: 320×240px each
- Cell borders: 1.5px, `#334155` at 0.4
- Cell background: `#0F172A` at 0.5

#### Axis Labels
- X-axis: "Greenfield" (left) → "Brownfield" (right) — Inter, 13px, semi-bold (600), `#94A3B8` at 0.5
- Y-axis: "In-Distribution" (top) → "Out-of-Distribution" (bottom) — Inter, 13px, semi-bold (600), `#94A3B8` at 0.5, rotated
- Arrows between labels: thin 1px, `#64748B` at 0.3

#### Top-Left Quadrant (green glow)
- Background: `#4ADE80` at 0.06
- Border highlight: `#4ADE80` at 0.2, 2px
- Label: "GitHub study:" — Inter, 12px, `#94A3B8` at 0.6
- Value: "+55%" — Inter, 28px, bold (700), `#4ADE80` at 0.9
- Glow: 20px Gaussian blur outward, `#4ADE80` at 0.08

#### Bottom-Right Quadrant (red glow)
- Background: `#EF4444` at 0.06
- Border highlight: `#EF4444` at 0.2, 2px
- Label: "METR study:" — Inter, 12px, `#94A3B8` at 0.6
- Value: "−19%" — Inter, 28px, bold (700), `#EF4444` at 0.9
- Glow: 20px Gaussian blur outward, `#EF4444` at 0.08

#### Top-Right Quadrant (neutral)
- Background: `#1E293B` at 0.15
- Label: "Mixed" — Inter, 12px, `#64748B` at 0.4

#### Bottom-Left Quadrant (neutral)
- Background: `#1E293B` at 0.15
- Label: "Mixed" — Inter, 12px, `#64748B` at 0.4

#### Summary Label
- "Every study is correct. They just measured different quadrants." — Inter, 16px, semi-bold (600), `#E2E8F0` at 0.7, centered at y: 800
- "And most real enterprise work lives in the bottom-right." — Inter, 13px, `#EF4444` at 0.5, centered at y: 835

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** 2×2 grid draws — borders appear, axis labels fade in.
2. **Frame 40-60 (1.33-2s):** Axis arrows and label text appear.
3. **Frame 60-180 (2-6s):** Top-left quadrant illuminates green. "+55%" counts up from 0. "GitHub study" label fades in.
4. **Frame 180-300 (6-10s):** Bottom-right quadrant illuminates red. "−19%" counts up (down) from 0. "METR study" label fades in.
5. **Frame 300-360 (10-12s):** Neutral quadrants get "Mixed" labels. Grid is complete.
6. **Frame 360-480 (12-16s):** Summary label types in at bottom: "Every study is correct. They just measured different quadrants."
7. **Frame 480-540 (16-18s):** Second line fades in: "And most real enterprise work lives in the bottom-right." Bottom-right quadrant pulses.
8. **Frame 540-660 (18-22s):** Hold on complete visualization.

### Typography
- Axis labels: Inter, 13px, semi-bold (600), `#94A3B8` at 0.5
- Quadrant source labels: Inter, 12px, `#94A3B8` at 0.6
- Quadrant values: Inter, 28px, bold (700), respective colors
- Summary: Inter, 16px, semi-bold (600), `#E2E8F0` at 0.7
- Enterprise note: Inter, 13px, `#EF4444` at 0.5

### Easing
- Grid border draw: `easeOut(cubic)` over 30 frames
- Quadrant illuminate: `easeOut(quad)` over 30 frames
- Number count: `easeOut(quad)` over 30 frames
- Label fade: `easeOut(quad)` over 20 frames
- Summary type: character-by-character, 1.5 frames each
- Bottom-right pulse: `easeInOut(sine)` over 30 frames

## Narration Sync
> "The GitHub study measured greenfield, in-distribution work—exactly where AI shines. The METR study measured brownfield, out-of-distribution work—where AI flounders."
> "They're not contradictory. They're measuring different quadrants."

Segments: `part1_economics_023`

- **3:26** ("GitHub study measured greenfield"): Grid draws, top-left illuminates green
- **3:36** ("METR study measured brownfield"): Bottom-right illuminates red
- **3:42** ("not contradictory"): Summary label appears
- **3:48** ("different quadrants"): Enterprise note, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={660}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* 2×2 Grid */}
    <TwoByTwoGrid
      center={[960, 480]} cellWidth={320} cellHeight={240}
      borderColor="#334155" borderOpacity={0.4} borderWidth={1.5}
      drawDuration={30}>

      {/* Axis labels */}
      <AxisLabel axis="x" start="Greenfield" end="Brownfield"
        font="Inter" size={13} weight={600}
        color="#94A3B8" opacity={0.5} />
      <AxisLabel axis="y" start="In-Distribution" end="Out-of-Distribution"
        font="Inter" size={13} weight={600}
        color="#94A3B8" opacity={0.5} />

      {/* Top-left — green */}
      <Sequence from={60}>
        <QuadrantIlluminate position="top-left"
          color="#4ADE80" bgOpacity={0.06}
          borderOpacity={0.2} glowBlur={20} glowOpacity={0.08}>
          <Text text="GitHub study:" font="Inter" size={12}
            color="#94A3B8" opacity={0.6} />
          <CountUp value={55} prefix="+" suffix="%"
            font="Inter" size={28} weight={700}
            color="#4ADE80" duration={30} />
        </QuadrantIlluminate>
      </Sequence>

      {/* Bottom-right — red */}
      <Sequence from={180}>
        <QuadrantIlluminate position="bottom-right"
          color="#EF4444" bgOpacity={0.06}
          borderOpacity={0.2} glowBlur={20} glowOpacity={0.08}>
          <Text text="METR study:" font="Inter" size={12}
            color="#94A3B8" opacity={0.6} />
          <CountUp value={-19} suffix="%"
            font="Inter" size={28} weight={700}
            color="#EF4444" duration={30} />
        </QuadrantIlluminate>
      </Sequence>

      {/* Neutral quadrants */}
      <Sequence from={300}>
        <FadeIn duration={15}>
          <QuadrantLabel position="top-right" text="Mixed"
            color="#64748B" opacity={0.4} />
          <QuadrantLabel position="bottom-left" text="Mixed"
            color="#64748B" opacity={0.4} />
        </FadeIn>
      </Sequence>
    </TwoByTwoGrid>

    {/* Summary */}
    <Sequence from={360}>
      <TypeWriter
        text="Every study is correct. They just measured different quadrants."
        font="Inter" size={16} weight={600}
        color="#E2E8F0" opacity={0.7}
        charDelay={1.5} x={960} y={800} align="center" />
    </Sequence>

    <Sequence from={480}>
      <FadeIn duration={20}>
        <Text text="And most real enterprise work lives in the bottom-right."
          font="Inter" size={13} color="#EF4444" opacity={0.5}
          x={960} y={835} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "two_by_two_grid",
  "diagramId": "productivity_quadrant",
  "axes": {
    "x": { "start": "Greenfield", "end": "Brownfield" },
    "y": { "start": "In-Distribution", "end": "Out-of-Distribution" }
  },
  "quadrants": [
    {
      "position": "top-left",
      "label": "GitHub study",
      "value": "+55%",
      "color": "#4ADE80",
      "source": "GitHub, 2022"
    },
    {
      "position": "bottom-right",
      "label": "METR study",
      "value": "−19%",
      "color": "#EF4444",
      "source": "METR, 2025"
    },
    { "position": "top-right", "label": "Mixed", "color": "#64748B" },
    { "position": "bottom-left", "label": "Mixed", "color": "#64748B" }
  ],
  "summary": "Every study is correct. They just measured different quadrants.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_economics_023"]
}
```

---
