[Remotion]

# Section 1.6: Two-by-Two Grid — Why Every Study Is Correct

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 3:59 - 4:17

## Visual Description

A clean 2x2 grid appears, resolving the apparent contradiction between productivity studies. The X-axis goes from "Greenfield" (left) to "Brownfield" (right). The Y-axis goes from "In-Distribution" (top) to "Out-of-Distribution" (bottom).

The four quadrants fill in one by one:
- **Top-left** (Greenfield × In-Distribution) glows green: "GitHub study: +55%". This is the easy win — new code, familiar patterns.
- **Top-right** (Greenfield × Out-of-Distribution) shows yellow-amber: intermediate zone.
- **Bottom-left** (Brownfield × In-Distribution) shows yellow-amber: intermediate zone.
- **Bottom-right** (Brownfield × Out-of-Distribution) glows red: "METR study: −19%". This is real enterprise work — legacy code, unfamiliar territory.

A label appears below: "Every study is correct. They just measured different quadrants." Then a subtle highlight shows that most real enterprise work lives in the bottom-right quadrant — the red zone.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: None

### Chart/Visual Elements

#### Grid Container
- Center: (960, 480)
- Total size: 640x480
- Border: 2px, `#334155` at 0.4
- Internal dividers: 2px, `#334155` at 0.3

#### Axis Labels
- X-axis left: "Greenfield" — Inter, 16px, semi-bold (600), `#5AAA6E` at 0.6, positioned below grid at left
- X-axis right: "Brownfield" — Inter, 16px, semi-bold (600), `#EF4444` at 0.6, positioned below grid at right
- X-axis arrow: thin arrow from left to right, `#475569` at 0.3, below grid
- Y-axis top: "In-Distribution" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, rotated -90°, left of grid
- Y-axis bottom: "Out-of-Distribution" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, rotated -90°, left of grid
- Y-axis arrow: thin arrow from top to bottom, `#475569` at 0.3, left of grid

#### Quadrant — Top-Left (Greenfield × In-Distribution)
- Fill: `#5AAA6E` at 0.12
- Border glow: 4px, `#5AAA6E` at 0.15
- Main text: "+55%" — Inter, 36px, bold (700), `#5AAA6E`
- Subtitle: "GitHub study" — Inter, 12px, `#5AAA6E` at 0.5
- Fine print: "95 devs, greenfield" — Inter, 9px, `#64748B` at 0.3

#### Quadrant — Top-Right (Greenfield × Out-of-Distribution)
- Fill: `#D9944A` at 0.06
- Main text: "Moderate" — Inter, 18px, `#D9944A` at 0.4
- No specific study cited

#### Quadrant — Bottom-Left (Brownfield × In-Distribution)
- Fill: `#D9944A` at 0.06
- Main text: "Moderate" — Inter, 18px, `#D9944A` at 0.4
- No specific study cited

#### Quadrant — Bottom-Right (Brownfield × Out-of-Distribution)
- Fill: `#EF4444` at 0.10
- Border glow: 4px, `#EF4444` at 0.12
- Main text: "−19%" — Inter, 36px, bold (700), `#EF4444`
- Subtitle: "METR study" — Inter, 12px, `#EF4444` at 0.5
- Fine print: "experienced devs, mature repos" — Inter, 9px, `#64748B` at 0.3

#### Enterprise Indicator
- A dashed outline appears around the bottom-right quadrant
- Label: "Most enterprise work" — Inter, 11px, `#EF4444` at 0.4, with arrow pointing to bottom-right

#### Reconciliation Label
- Position: below grid at y: 820
- Text: "Every study is correct. They just measured different quadrants."
- Inter, 18px, semi-bold (600), `#E2E8F0` at 0.8
- Background: subtle pill, `#1E293B` at 0.3, rounded 12px, padding 16px

### Animation Sequence
1. **Frame 0-40 (0-1.3s):** Grid container draws in — borders, dividers, axis labels.
2. **Frame 40-120 (1.3-4s):** Top-left quadrant fills green. "+55%" appears with scale bounce. "GitHub study" subtitle fades in.
3. **Frame 120-180 (4-6s):** Bottom-right quadrant fills red. "−19%" appears with scale bounce. "METR study" subtitle fades in. The diagonal contrast is stark.
4. **Frame 180-240 (6-8s):** Middle quadrants fill with amber — "Moderate" labels appear. The gradient from green to red across the diagonal is complete.
5. **Frame 240-330 (8-11s):** Enterprise indicator — dashed outline around bottom-right, "Most enterprise work" label with arrow.
6. **Frame 330-420 (11-14s):** Reconciliation label slides up from bottom: "Every study is correct. They just measured different quadrants."
7. **Frame 420-540 (14-18s):** Hold. The grid is the argument. Both extremes are validated.

### Typography
- Quadrant percentages: Inter, 36px, bold (700), respective colors
- Quadrant subtitles: Inter, 12px, respective colors at 0.5
- Fine print: Inter, 9px, `#64748B` at 0.3
- Axis labels: Inter, 14-16px, semi-bold (600), respective colors
- Reconciliation text: Inter, 18px, semi-bold (600), `#E2E8F0`
- Enterprise label: Inter, 11px, `#EF4444` at 0.4

### Easing
- Grid draw: `easeOut(cubic)` over 30 frames
- Quadrant fill: `easeOut(quad)` over 20 frames
- Percentage appear: `easeOut(back(1.3))` scale from 0.7 to 1.0, 15 frames
- Enterprise indicator: `easeOut(quad)` over 20 frames
- Reconciliation slide: `easeOut(cubic)` from y+20, 25 frames

## Narration Sync
> "This is why AI-assisted patching is really two stories — and why every productivity study seems to contradict every other one."
> "The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI flounders. They're not contradictory. They're measuring different quadrants. And most real enterprise work? It lives in the bottom-right."

Segment: `part1_006`

- **3:59** ("This is why AI-assisted patching is really two stories"): Grid container appears
- **4:03** ("GitHub study measured greenfield"): Top-left quadrant fills green
- **4:07** ("METR study measured brownfield"): Bottom-right quadrant fills red
- **4:11** ("They're measuring different quadrants"): All quadrants visible, reconciliation label appears
- **4:15** ("most real enterprise work"): Enterprise indicator highlights bottom-right

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Grid container with axes */}
    <Sequence from={0}>
      <TwoByTwoGrid
        center={[960, 480]} size={[640, 480]}
        borderColor="#334155" dividerColor="#334155"
        xLabels={{ left: 'Greenfield', right: 'Brownfield' }}
        yLabels={{ top: 'In-Distribution', bottom: 'Out-of-Distribution' }}
        drawDuration={30}
      />
    </Sequence>

    {/* Top-left: GitHub +55% */}
    <Sequence from={40}>
      <QuadrantFill
        quadrant="top-left"
        fillColor="#5AAA6E" fillOpacity={0.12}
        glowColor="#5AAA6E" glowWidth={4}
        mainText="+55%" mainSize={36} mainColor="#5AAA6E"
        subtitle="GitHub study" subtitleSize={12}
        finePrint="95 devs, greenfield"
      />
    </Sequence>

    {/* Bottom-right: METR -19% */}
    <Sequence from={120}>
      <QuadrantFill
        quadrant="bottom-right"
        fillColor="#EF4444" fillOpacity={0.10}
        glowColor="#EF4444" glowWidth={4}
        mainText="−19%" mainSize={36} mainColor="#EF4444"
        subtitle="METR study" subtitleSize={12}
        finePrint="experienced devs, mature repos"
      />
    </Sequence>

    {/* Middle quadrants */}
    <Sequence from={180}>
      <QuadrantFill quadrant="top-right"
        fillColor="#D9944A" fillOpacity={0.06}
        mainText="Moderate" mainSize={18} mainColor="#D9944A" />
      <QuadrantFill quadrant="bottom-left"
        fillColor="#D9944A" fillOpacity={0.06}
        mainText="Moderate" mainSize={18} mainColor="#D9944A" />
    </Sequence>

    {/* Enterprise indicator */}
    <Sequence from={240}>
      <DashedOutline quadrant="bottom-right"
        color="#EF4444" opacity={0.4}
        label="Most enterprise work" />
    </Sequence>

    {/* Reconciliation label */}
    <Sequence from={330}>
      <SlideUp distance={20} duration={25}>
        <PillLabel
          text="Every study is correct. They just measured different quadrants."
          font="Inter" size={18} weight={600}
          color="#E2E8F0" bgColor="#1E293B"
          x={960} y={820}
        />
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "quadrant_grid",
  "diagramId": "two_by_two_productivity",
  "axes": {
    "x": { "left": "Greenfield", "right": "Brownfield" },
    "y": { "top": "In-Distribution", "bottom": "Out-of-Distribution" }
  },
  "quadrants": [
    {
      "position": "top-left",
      "label": "+55%",
      "source": "GitHub, 2022",
      "color": "#5AAA6E",
      "sentiment": "positive"
    },
    {
      "position": "top-right",
      "label": "Moderate",
      "color": "#D9944A",
      "sentiment": "neutral"
    },
    {
      "position": "bottom-left",
      "label": "Moderate",
      "color": "#D9944A",
      "sentiment": "neutral"
    },
    {
      "position": "bottom-right",
      "label": "−19%",
      "source": "METR, 2025",
      "color": "#EF4444",
      "sentiment": "negative",
      "enterpriseWork": true
    }
  ],
  "reconciliation": "Every study is correct. They just measured different quadrants.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part1_006"]
}
```

---
