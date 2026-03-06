[Remotion] Dual-Line Cost Crossover Chart Overlay

# Section 1.2: Cost Crossover Chart — Patching vs Generation

**Tool:** Remotion
**Duration:** ~90s (Acts A-B primary, returns Act G)
**Timestamp:** 0:05 - 2:30 (primary draw-in), 6:15 - 6:22 (dramatic zoom return)

## Visual Description
An animated dual-line chart overlaid on the Veo cost graph background. The chart features two lines that animate sequentially: the "cost of patching" line (amber/red) draws itself upward from left to right, while the "cost of generation" line (blue/green) draws itself downward. A dashed "total cost of ownership" line barely moves, hovering at the top. Axis labels, data annotations, and a crossover callout animate in with precise timing. During Act G, the chart zooms dramatically to the intersection point with a pulsing glow effect.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Chart area: 200px padding left/bottom, 100px padding right/top → chart region (200, 80) to (1820, 880)

### Chart/Visual Elements
- X-axis: "Time / Codebase Size" — left="Small / New" to right="Large / Mature"
- Y-axis: "Cost per Change" — bottom=$0 to top=labeled range
- Line A (patching): #EF4444 → #F59E0B gradient stroke, 4px width, starts low-left, curves upward to high-right
- Line B (generation): #3B82F6 → #22C55E gradient stroke, 4px width, starts high-left, curves downward to low-right
- Line C (total cost): #94A3B8 dashed stroke, 2px width, nearly flat with slight upward trend
- Crossover point: white circle (12px) with pulsing glow ring (#F59E0B, 30px radius, pulsing opacity 40%→80%)
- Crossover label: "Crossover" with downward arrow, appears above intersection
- Grid lines: horizontal dashed lines at 25%, 50%, 75% of Y range, #334155 at 15% opacity

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in — X and Y axis lines, tick marks, labels. Opacity 0→1.
2. **Frame 30-90 (1-3s):** Grid lines fade in subtly. Opacity 0→0.15.
3. **Frame 60-180 (2-6s):** Line A (patching cost) draws from left to right — SVG path dashoffset animation.
4. **Frame 120-240 (4-8s):** Line B (generation cost) draws from left to right — SVG path dashoffset animation (starts 2s after Line A).
5. **Frame 200-260 (6.67-8.67s):** Line C (total cost) fades in — dashed line, opacity 0→0.6.
6. **Frame 250-280 (8.33-9.33s):** Crossover point appears — white dot scales 0→1, glow ring pulses.
7. **Frame 280-310 (9.33-10.33s):** "Crossover" label fades in with downward arrow.
8. **Frame 310-2700 (10.33-90s):** Hold. Crossover glow continues pulsing. (Other overlays appear on top.)
9. **Act G Return (frame ~11100):** Chart zooms — scale 1.0→2.5, centering on crossover point. Glow intensifies.

### Typography
- Axis labels: Inter Medium, 18px, #94A3B8
- Axis title (X): Inter Medium, 20px, #CBD5E1, centered below X-axis
- Axis title (Y): Inter Medium, 20px, #CBD5E1, rotated 90°, left of Y-axis
- Line labels: Inter SemiBold, 22px, matching line color, positioned at line endpoints
  - "Cost of Patching" — right end of Line A, #EF4444
  - "Cost of Generation" — right end of Line B, #3B82F6
  - "Total Cost" — right end of Line C, #94A3B8
- Crossover label: Inter Bold, 24px, #FFFFFF

### Easing
- Axis fade in: `easeOutCubic`
- Line draw: `easeInOutQuad`
- Crossover dot scale: `spring({ damping: 12, stiffness: 200 })`
- Crossover glow pulse: sinusoidal, 2s period
- Act G zoom: `easeInOutCubic`

## Narration Sync
> "Sometime in the late 1950s, the cost of materials — cotton, nylon, elastic — was higher than the cost of labor. Then by the early 1960s, the economics flipped. Mass production made socks so cheap that darning wasn't worth anyone's time."

Axes and grid appear as the economic framing begins. Lines draw as the narration describes cost curves. Crossover point appears as "the economics flipped."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={2700}>
  <AbsoluteFill>
    {/* Axes and grid */}
    <Sequence from={0} durationInFrames={90}>
      <ChartAxes
        xLabel="Time / Codebase Size"
        yLabel="Cost per Change"
        opacity={interpolate(frame, [0, 30], [0, 1])}
        gridOpacity={interpolate(frame, [30, 90], [0, 0.15])}
      />
    </Sequence>

    {/* Patching cost line — draws in */}
    <Sequence from={60} durationInFrames={120}>
      <AnimatedLine
        data={patchingCostData}
        stroke="url(#patchingGradient)"
        strokeWidth={4}
        drawProgress={interpolate(frame, [0, 120], [0, 1], { easing: Easing.inOut(Easing.quad) })}
      />
    </Sequence>

    {/* Generation cost line — draws in */}
    <Sequence from={120} durationInFrames={120}>
      <AnimatedLine
        data={generationCostData}
        stroke="url(#generationGradient)"
        strokeWidth={4}
        drawProgress={interpolate(frame, [0, 120], [0, 1], { easing: Easing.inOut(Easing.quad) })}
      />
    </Sequence>

    {/* Total cost line */}
    <Sequence from={200} durationInFrames={60}>
      <AnimatedLine
        data={totalCostData}
        stroke="#94A3B8"
        strokeWidth={2}
        dashArray="8 6"
        opacity={interpolate(frame, [0, 60], [0, 0.6])}
      />
    </Sequence>

    {/* Crossover point */}
    <Sequence from={250} durationInFrames={2450}>
      <CrossoverPoint
        position={crossoverXY}
        dotScale={spring({ frame: frame - 250, fps: 30, config: { damping: 12, stiffness: 200 } })}
        glowOpacity={interpolate(Math.sin(frame * 0.105), [-1, 1], [0.4, 0.8])}
      />
      <Sequence from={30}>
        <CrossoverLabel text="Crossover" opacity={interpolate(frame, [0, 30], [0, 1])} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "patching_cost": {
    "label": "Cost of Patching",
    "color_start": "#EF4444",
    "color_end": "#F59E0B",
    "points": [
      {"x": 0, "y": 0.15},
      {"x": 0.2, "y": 0.22},
      {"x": 0.4, "y": 0.35},
      {"x": 0.6, "y": 0.55},
      {"x": 0.8, "y": 0.78},
      {"x": 1.0, "y": 0.95}
    ]
  },
  "generation_cost": {
    "label": "Cost of Generation",
    "color_start": "#3B82F6",
    "color_end": "#22C55E",
    "points": [
      {"x": 0, "y": 0.90},
      {"x": 0.2, "y": 0.72},
      {"x": 0.4, "y": 0.50},
      {"x": 0.6, "y": 0.35},
      {"x": 0.8, "y": 0.25},
      {"x": 1.0, "y": 0.18}
    ]
  },
  "total_cost": {
    "label": "Total Cost of Ownership",
    "color": "#94A3B8",
    "points": [
      {"x": 0, "y": 0.82},
      {"x": 0.2, "y": 0.83},
      {"x": 0.4, "y": 0.84},
      {"x": 0.6, "y": 0.86},
      {"x": 0.8, "y": 0.87},
      {"x": 1.0, "y": 0.88}
    ]
  },
  "crossover": {"x": 0.42, "y": 0.48},
  "chart_frames": 2700,
  "fps": 30
}
```

---
