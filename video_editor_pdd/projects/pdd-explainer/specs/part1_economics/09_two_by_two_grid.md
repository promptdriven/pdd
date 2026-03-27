[Remotion]

# Section 1.9: 2×2 Study Grid — Greenfield vs. Brownfield, In- vs. Out-of-Distribution

**Tool:** Remotion
**Duration:** ~21s (630 frames @ 30fps)
**Timestamp:** 4:38 - 4:59

## Visual Description

A clean 2×2 matrix appears, resolving the apparent contradiction between productivity studies. This is the "reconciliation" beat — showing that every study is correct, just measuring different conditions.

**Axes:**
- X-axis: "Greenfield → Brownfield"
- Y-axis: "In-Distribution → Out-of-Distribution"

**Quadrants:**
- Top-left (greenfield + in-distribution): Glows GREEN. Label: "GitHub study: +55%"
- Bottom-right (brownfield + out-of-distribution): Glows RED. Label: "METR study: −19%"
- Top-right and bottom-left: Intermediate, neutral gray

**Key label** below the grid: "Every study is correct. They just measured different quadrants."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Grid
- Total grid size: 600×600px, centered at (960, 480)
- Divider lines: `#334155`, 2px
- Cell size: 300×300px each

#### Quadrant Fills
- Top-left: `#5AAA6E` at 0.15, border glow `#5AAA6E` at 0.3
- Top-right: `#64748B` at 0.06 (neutral)
- Bottom-left: `#64748B` at 0.06 (neutral)
- Bottom-right: `#EF4444` at 0.15, border glow `#EF4444` at 0.3

#### Axis Labels
- X-axis: "Greenfield" (left) and "Brownfield" (right) — Inter 16px, `#94A3B8`
- Y-axis: "In-Distribution" (top) and "Out-of-Distribution" (bottom) — Inter 16px, `#94A3B8`
- Arrows: Subtle gradient arrows along each axis

#### Quadrant Labels
- Top-left: "GitHub study: +55%" — Inter 20px, bold (700), `#5AAA6E`
- Bottom-right: "METR study: −19%" — Inter 20px, bold (700), `#EF4444`

#### Key Insight Label
- "Every study is correct. They just measured different quadrants." — Inter 16px, regular (400), `#E2E8F0`, centered below grid at y: 830

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Grid lines draw. Axis labels fade in.
2. **Frame 45-90 (1.5-3s):** Top-left quadrant illuminates green. "GitHub study: +55%" types in.
3. **Frame 90-150 (3-5s):** Hold on green quadrant.
4. **Frame 150-210 (5-7s):** Bottom-right quadrant illuminates red. "METR study: −19%" types in.
5. **Frame 210-390 (7-13s):** Both quadrants glowing. The contrast is clear.
6. **Frame 390-450 (13-15s):** Key insight label fades in below: "Every study is correct..."
7. **Frame 450-630 (15-21s):** Hold. Full grid visible with insight text.

### Typography
- Axis labels: Inter, 16px, regular (400), `#94A3B8`
- Quadrant labels: Inter, 20px, bold (700), respective colors
- Insight text: Inter, 16px, regular (400), `#E2E8F0`

### Easing
- Grid draw: `easeOut(quad)` over 30 frames
- Quadrant fill: `easeOut(cubic)` over 30 frames
- Label type-in: 2 frames per character
- Insight text: `easeOut(quad)` over 30 frames

## Narration Sync
> "The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI flounders. They're not contradictory. They're measuring different quadrants."

Segment: `part1_economics_019`

- **277.74s** (seg 019): Grid draws — "The GitHub study measured greenfield"
- **285.0s**: Green quadrant illuminates
- **290.0s**: Red quadrant illuminates
- **295.0s**: "They're measuring different quadrants" — insight text appears
- **298.94s** (seg 019 ends): Full grid visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={630}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Grid lines and axes */}
    <Sequence from={0}>
      <TwoByTwoGrid
        size={600} center={{ x: 960, y: 480 }}
        lineColor="#334155" lineWidth={2}
        xLabels={["Greenfield", "Brownfield"]}
        yLabels={["In-Distribution", "Out-of-Distribution"]}
        labelColor="#94A3B8" labelSize={16}
      />
    </Sequence>

    {/* Top-left quadrant: green */}
    <Sequence from={45}>
      <QuadrantFill
        position="top-left" color="#5AAA6E"
        fillOpacity={0.15} glowOpacity={0.3}
        label="GitHub study: +55%"
        labelColor="#5AAA6E" labelSize={20}
      />
    </Sequence>

    {/* Bottom-right quadrant: red */}
    <Sequence from={150}>
      <QuadrantFill
        position="bottom-right" color="#EF4444"
        fillOpacity={0.15} glowOpacity={0.3}
        label="METR study: −19%"
        labelColor="#EF4444" labelSize={20}
      />
    </Sequence>

    {/* Key insight */}
    <Sequence from={390}>
      <FadeIn duration={30}>
        <Text
          text="Every study is correct. They just measured different quadrants."
          font="Inter" size={16} color="#E2E8F0"
          x={960} y={830} align="center"
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "two_by_two_matrix",
  "chartId": "study_reconciliation_grid",
  "axes": {
    "x": { "labels": ["Greenfield", "Brownfield"] },
    "y": { "labels": ["In-Distribution", "Out-of-Distribution"] }
  },
  "quadrants": [
    {
      "position": "top-left",
      "color": "#5AAA6E",
      "label": "GitHub study: +55%",
      "source": "GitHub, 2022"
    },
    {
      "position": "bottom-right",
      "color": "#EF4444",
      "label": "METR study: −19%",
      "source": "METR, 2025"
    }
  ],
  "insightText": "Every study is correct. They just measured different quadrants.",
  "narrationSegments": ["part1_economics_019"]
}
```

---
