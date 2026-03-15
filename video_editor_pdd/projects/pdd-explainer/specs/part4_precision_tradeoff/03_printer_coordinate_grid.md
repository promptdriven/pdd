[Remotion]

# Section 4.3: 3D Printer — Coordinate Precision Close-Up

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 18:42 - 18:52

## Visual Description
A close-up view of the 3D printer metaphor, now occupying the full screen. A large coordinate grid fills the canvas with numbered axes. A nozzle head traces a complex shape — every coordinate is explicitly labeled as it deposits. Small coordinate labels (like "(7, 3)", "(8, 3)", "(8, 4)") appear next to each deposited point, emphasizing the extreme specificity required. The trail of deposited material gradually reveals the outline of a code function shape (suggestive of a bracket or curly brace). A counter in the corner tracks "Points specified: N" and increments with each deposit. The mood is meticulous and exhausting — visually communicating that specifying every detail is laborious.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Full coordinate grid, `rgba(255,255,255,0.06)`, 48px spacing

### Chart/Visual Elements
- **X-Axis:** Bottom edge, numbered 0-38 at every 4th gridline, labels in `#64748B`, 11px, JetBrains Mono
- **Y-Axis:** Left edge, numbered 0-20 at every 4th gridline, labels in `#64748B`, 11px, JetBrains Mono
- **Nozzle Head:** Inverted triangle, 20px wide, `#4A90D9` at 0.9 opacity, with a faint downward beam `rgba(74,144,217,0.3)` extending 8px below
- **Deposited Points:** Circles, 8px diameter, `#4A90D9` at 0.7 opacity, slight glow `rgba(74,144,217,0.3)` 12px radius
- **Coordinate Labels:** Appear beside each deposited point, e.g., "(12, 8)", JetBrains Mono 10px, `#4A90D9` at 0.4 opacity, offset 14px right and 4px up
- **Path Trace:** Connecting line between deposited points, `#4A90D9` at 0.25 opacity, 1px
- **Points Counter:** Top-right corner, "Points specified: {N}" — JetBrains Mono 16px, `#94A3B8` at 0.7 opacity, positioned at (1680, 40)
- **Section Label:** Top-left, "No mold. Every point explicit." — Inter 18px, `#94A3B8` at 0.5 opacity, positioned at (60, 40)

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Coordinate grid fades in with axes. Section label and counter ("Points specified: 0") fade in
2. **Frame 30-240 (1.0-8.0s):** Nozzle begins depositing points along a curly-brace-like path. Each deposit takes ~14 frames: nozzle moves to position (6 frames), deposits point with brief flash (4 frames), coordinate label fades in (4 frames). Counter increments with each deposit. ~15 points total deposited, tracing the shape
3. **Frame 180-240 (6.0-8.0s):** Pace accelerates — deposits speed up to ~10 frames each, coordinate labels begin overlapping, creating visual density. Counter climbs faster. Communicates tedium of point-by-point specification
4. **Frame 240-270 (8.0-9.0s):** Nozzle pauses. All deposited points and labels visible. The shape is only ~40% complete despite all the effort. A faint ghost outline shows how much remains, in `rgba(255,255,255,0.08)`
5. **Frame 270-300 (9.0-10.0s):** Hold. Counter reads "Points specified: 15" (of ~40 needed). The incompleteness emphasizes the cost of explicit specification

### Typography
- Axis Labels: JetBrains Mono, 11px, regular (400), `#64748B`
- Coordinate Labels: JetBrains Mono, 10px, regular (400), `#4A90D9` at 0.4 opacity
- Points Counter: JetBrains Mono, 16px, medium (500), `#94A3B8` at 0.7 opacity
- Section Label: Inter, 18px, regular (400), `#94A3B8` at 0.5 opacity

### Easing
- Grid fade-in: `easeOut(quad)`
- Nozzle movement (per step): `easeInOut(cubic)` (smooth mechanical motion)
- Point deposit flash: `easeOut(expo)`
- Coordinate label fade: `easeOut(quad)`
- Counter increment: `steps(1)` (discrete)
- Ghost outline: `easeIn(quad)`

## Narration Sync
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Coordinate Grid */}
  <Sequence from={0} durationInFrames={30}>
    <CoordinateGrid
      cols={38}
      rows={20}
      spacing={48}
      gridColor="rgba(255,255,255,0.06)"
      axisLabelColor="#64748B"
    />
  </Sequence>

  {/* Section Label */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn>
      <Label text="No mold. Every point explicit." x={60} y={40} color="#94A3B8" />
    </FadeIn>
  </Sequence>

  {/* Nozzle Depositor with Coordinate Labels */}
  <Sequence from={30} durationInFrames={210}>
    <NozzleWithLabels
      path={curlyBracePath}
      dotColor="#4A90D9"
      labelColor="rgba(74,144,217,0.4)"
      framesPerDot={14}
      accelerateAfterFrame={150}
      acceleratedFramesPerDot={10}
    />
  </Sequence>

  {/* Points Counter */}
  <Sequence from={0} durationInFrames={300}>
    <PointsCounter x={1680} y={40} color="#94A3B8" totalPoints={15} />
  </Sequence>

  {/* Ghost Outline (remaining shape) */}
  <Sequence from={240} durationInFrames={30}>
    <GhostOutline path={remainingPath} color="rgba(255,255,255,0.08)" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "grid": {
    "cols": 38,
    "rows": 20,
    "spacing": 48,
    "lineColor": "rgba(255,255,255,0.06)"
  },
  "depositPath": [
    [12, 8], [13, 7], [14, 6], [15, 6], [16, 5],
    [17, 5], [18, 5], [19, 6], [19, 7], [18, 8],
    [19, 9], [19, 10], [18, 11], [17, 11], [16, 11]
  ],
  "dotStyle": {
    "diameter": 8,
    "color": "#4A90D9",
    "opacity": 0.7,
    "glowRadius": 12,
    "glowColor": "rgba(74,144,217,0.3)"
  },
  "nozzle": {
    "width": 20,
    "color": "#4A90D9",
    "opacity": 0.9,
    "beamLength": 8,
    "beamColor": "rgba(74,144,217,0.3)"
  },
  "counter": {
    "label": "Points specified",
    "totalDeposited": 15,
    "totalNeeded": 40
  }
}
```

---
