[Remotion]

# Section 1.6: Productivity Study 2x2 Grid

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 3:43 - 3:55

## Visual Description
A clean 2x2 grid framework that explains why AI productivity studies seem to contradict each other. The X-axis runs from "Greenfield" (left) to "Brownfield" (right). The Y-axis runs from "In-Distribution" (top) to "Out-of-Distribution" (bottom). Each quadrant fills in sequentially with a color and study citation. Top-left glows green (GitHub: +55%), bottom-right glows red (METR: -19%). The middle quadrants are intermediate amber. A final label appears: "Every study is correct. They just measured different quadrants." with a subtle callout: "Most enterprise work lives here" pointing to the bottom-right.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Grid Container:** 800x600px, centered at (960, 500)
- **Grid Dividers:** 2px solid `rgba(255,255,255,0.2)`, one vertical at center, one horizontal at center
- **X-Axis Label (Top):** "Greenfield" (left) → "Brownfield" (right), positioned at Y=160px
  - Arrow: thin `rgba(255,255,255,0.3)` connecting the two labels
- **Y-Axis Label (Left):** "In-Distribution" (top) → "Out-of-Distribution" (bottom), positioned at X=480px
  - Arrow: thin `rgba(255,255,255,0.3)` connecting vertically
- **Quadrant A (Top-Left):** Greenfield × In-Distribution
  - Fill: `rgba(34, 197, 94, 0.15)` (green tint)
  - Border glow: `rgba(34, 197, 94, 0.3)`
  - Stat: "+55%" in `#22C55E`, 42px bold
  - Citation: "GitHub, 2022" in `#94A3B8`, 14px
- **Quadrant B (Top-Right):** Brownfield × In-Distribution
  - Fill: `rgba(245, 158, 11, 0.1)` (amber tint)
  - Stat: "~0%" in `#F59E0B`, 36px bold
  - Label: "Mixed results" in `#94A3B8`, 14px
- **Quadrant C (Bottom-Left):** Greenfield × Out-of-Distribution
  - Fill: `rgba(245, 158, 11, 0.1)` (amber tint)
  - Stat: "Varies" in `#F59E0B`, 36px bold
  - Label: "Task-dependent" in `#94A3B8`, 14px
- **Quadrant D (Bottom-Right):** Brownfield × Out-of-Distribution
  - Fill: `rgba(239, 68, 68, 0.15)` (red tint)
  - Border glow: `rgba(239, 68, 68, 0.3)`
  - Stat: "-19%" in `#EF4444`, 42px bold
  - Citation: "METR, 2025" in `#94A3B8`, 14px
  - Callout arrow from label "Most enterprise work lives here" in `#F59E0B`, 16px
- **Summary Text:** Centered at Y=840px — "Every study is correct. They just measured different quadrants." in `#FFFFFF`, 22px

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Grid frame draws in — dividers, axes, and axis labels fade in simultaneously
2. **Frame 40-100 (1.33-3.33s):** Quadrant A (top-left) fills green. "+55%" stat badge scales in. "GitHub, 2022" fades in
3. **Frame 100-160 (3.33-5.33s):** Quadrant D (bottom-right) fills red. "-19%" stat scales in. "METR, 2025" fades in. The diagonal contrast is stark
4. **Frame 160-220 (5.33-7.33s):** Quadrants B and C fill amber simultaneously with their labels. The full picture emerges
5. **Frame 220-280 (7.33-9.33s):** "Most enterprise work lives here" callout draws in — a curved arrow points from the text to Quadrant D. The arrow pulses once
6. **Frame 280-320 (9.33-10.67s):** Summary text fades in at bottom: "Every study is correct. They just measured different quadrants."
7. **Frame 320-360 (10.67-12.0s):** Hold. Subtle pulse on the red/green diagonal

### Typography
- Axis Labels: Inter, 18px, semi-bold (600), `#FFFFFF`, opacity 0.7
- Stat Badges: Inter, 42px (36px for middle quadrants), bold (800)
- Citations: Inter, 14px, regular (400), `#94A3B8`
- Quadrant Labels: Inter, 14px, regular (400), `#94A3B8`
- Summary: Inter, 22px, regular (400), `#FFFFFF`, opacity 0.9
- "Most enterprise work" Callout: Inter, 16px, semi-bold (600), `#F59E0B`

### Easing
- Grid draw: `easeOut(cubic)`
- Quadrant fill: `easeOut(quad)` — color fades in
- Stat badge scale: `easeOut(back(1.2))`
- Callout arrow: `easeOut(cubic)` — draws along curved path
- Summary text: `easeOut(quad)`

## Narration Sync
> "This is why AI-assisted patching is really two stories — and why every productivity study seems to contradict every other one."
> "The GitHub study measured greenfield, in-distribution work — exactly where AI shines. The METR study measured brownfield, out-of-distribution work — where AI flounders. They're not contradictory. They're measuring different quadrants. And most real enterprise work? It lives in the bottom-right."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  {/* Grid Frame */}
  <Sequence from={0} durationInFrames={40}>
    <GridFrame width={800} height={600} center={[960, 500]} />
    <AxisLabels
      xLabels={["Greenfield", "Brownfield"]}
      yLabels={["In-Distribution", "Out-of-Distribution"]}
    />
  </Sequence>

  {/* Quadrant A — Green */}
  <Sequence from={40} durationInFrames={60}>
    <Quadrant
      position="top-left"
      fillColor="rgba(34, 197, 94, 0.15)"
      stat="+55%"
      statColor="#22C55E"
      citation="GitHub, 2022"
    />
  </Sequence>

  {/* Quadrant D — Red */}
  <Sequence from={100} durationInFrames={60}>
    <Quadrant
      position="bottom-right"
      fillColor="rgba(239, 68, 68, 0.15)"
      stat="-19%"
      statColor="#EF4444"
      citation="METR, 2025"
    />
  </Sequence>

  {/* Quadrants B & C — Amber */}
  <Sequence from={160} durationInFrames={60}>
    <Quadrant position="top-right" stat="~0%" statColor="#F59E0B" label="Mixed results" />
    <Quadrant position="bottom-left" stat="Varies" statColor="#F59E0B" label="Task-dependent" />
  </Sequence>

  {/* Enterprise Callout */}
  <Sequence from={220} durationInFrames={60}>
    <CurvedCallout
      text="Most enterprise work lives here"
      target="bottom-right"
      color="#F59E0B"
    />
  </Sequence>

  {/* Summary */}
  <Sequence from={280}>
    <SummaryText text="Every study is correct. They just measured different quadrants." />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "grid": {
    "width": 800,
    "height": 600,
    "center": [960, 500]
  },
  "axes": {
    "x": ["Greenfield", "Brownfield"],
    "y": ["In-Distribution", "Out-of-Distribution"]
  },
  "quadrants": [
    {
      "position": "top-left",
      "stat": "+55%",
      "statColor": "#22C55E",
      "fill": "rgba(34, 197, 94, 0.15)",
      "citation": "GitHub, 2022",
      "description": "Greenfield, in-distribution"
    },
    {
      "position": "top-right",
      "stat": "~0%",
      "statColor": "#F59E0B",
      "fill": "rgba(245, 158, 11, 0.1)",
      "label": "Mixed results",
      "description": "Brownfield, in-distribution"
    },
    {
      "position": "bottom-left",
      "stat": "Varies",
      "statColor": "#F59E0B",
      "fill": "rgba(245, 158, 11, 0.1)",
      "label": "Task-dependent",
      "description": "Greenfield, out-of-distribution"
    },
    {
      "position": "bottom-right",
      "stat": "-19%",
      "statColor": "#EF4444",
      "fill": "rgba(239, 68, 68, 0.15)",
      "citation": "METR, 2025",
      "description": "Brownfield, out-of-distribution"
    }
  ],
  "summary": "Every study is correct. They just measured different quadrants.",
  "backgroundColor": "#0F172A"
}
```

---
