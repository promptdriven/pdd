[split:]

# Section 4.2: 3D Printer vs Injection Mold — Split Screen

**Tool:** Split
**Duration:** ~20s (601 frames @ 30fps)
**Timestamp:** 0:07 - 0:27

## Visual Description

A vertical split screen establishing the central metaphor. The split persists across three narration beats: the initial comparison, the 3D printer focus, and the injection mold focus.

**LEFT — "3D PRINTING":** A stylized top-down view of a 3D printer nozzle depositing material layer by layer. A coordinate grid overlays the scene — every deposited point is precisely addressed with (x, y, z) coordinates. Dotted guide lines connect each deposited point to the axes. The nozzle moves methodically, slowly. A label reads "Every point must be specified." During the focus beat, the grid brightens and coordinate labels appear: individual (x, y) markers at each deposited point.

**RIGHT — "INJECTION MOLDING":** A cross-section of a mold with liquid flowing in from a nozzle at the top. The liquid flows freely — chaotic, organic, spreading — until it hits the hard walls of the mold. The walls constrain the shape. A label reads "Walls do the precision work." During the focus beat, the walls glow amber and the liquid settles into its final constrained shape.

The contrast is immediate: left side = explicit precision at every point; right side = emergent precision from constraints.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — 3D Printing
- Header: "3D PRINTING" — Inter, 20px, bold, `#60A5FA` at 0.7, centered at y: 80
- Nozzle: inverted triangle (20×15px), `#60A5FA` at 0.8, starts at (240, 200)
- Deposited material: series of small rectangles (6×3px) forming layers, `#60A5FA` at 0.6
- Coordinate grid: dashed lines at 40px intervals, `#60A5FA` at 0.08
- Axis labels: x-axis (0-200) and y-axis (0-200), Inter, 9px, `#60A5FA` at 0.3
- Coordinate markers: (x,y) labels at deposited points, JetBrains Mono, 8px, `#60A5FA` at 0.4
- Caption: "Every point must be specified" — Inter, 14px, `#60A5FA` at 0.5, centered at y: 950

#### Right Panel — Injection Molding
- Header: "INJECTION MOLDING" — Inter, 20px, bold, `#D9944A` at 0.7, centered at y: 80
- Mold walls: thick rectangular outline (300×400px), centered at (1440, 500), `#D9944A` at 0.6, 4px stroke
- Internal wall shapes: 3 irregular step shapes inside mold, `#D9944A` at 0.5, 3px stroke
- Liquid: amorphous blob shape, `#A78BFA` at 0.4, flowing from top nozzle
- Nozzle (top): tapered shape pointing into mold top, `#94A3B8` at 0.5
- Caption: "Walls do the precision work" — Inter, 14px, `#D9944A` at 0.5, centered at y: 950

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in. Both headers appear.
2. **Frame 15-90 (0.5-3s):** LEFT: Coordinate grid draws in. Nozzle appears and begins depositing first layer of material, point by point. RIGHT: Mold walls draw in with stroke animation.
3. **Frame 90-210 (3-7s):** LEFT: Nozzle continues depositing — 3 layers built up. Each deposited point gets a brief coordinate label flash. Grid brightens. RIGHT: Liquid begins flowing from nozzle into mold. Chaotic, organic flow animation.
4. **Frame 210-390 (7-13s):** LEFT: Focus beat — coordinate grid becomes more prominent. Individual (x,y) labels appear at each deposited point sequentially. Nozzle slows to emphasize precision. RIGHT: Liquid spreads until it hits walls. Walls glow amber on impact. Liquid settles into constrained shape.
5. **Frame 390-510 (13-17s):** LEFT: Grid pulses. All coordinate markers visible. Caption appears. RIGHT: Final shape complete. Walls glowing. Caption appears.
6. **Frame 510-601 (17-20s):** Hold. Both sides complete. Gentle pulse on key elements.

### Typography
- Headers: Inter, 20px, bold (700), respective panel color at 0.7
- Coordinate labels: JetBrains Mono, 8px, `#60A5FA` at 0.4
- Axis labels: Inter, 9px, `#60A5FA` at 0.3
- Captions: Inter, 14px, respective panel color at 0.5

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Grid draw: `easeInOut(cubic)` over 40 frames
- Nozzle deposit: linear for each point, `easeOut(quad)` for layer transitions
- Liquid flow: `easeInOut(sine)` with noise offset for organic feel
- Wall glow on impact: `easeOut(cubic)` over 15 frames
- Coordinate label flash: `easeOut(quad)` over 10 frames, staggered 3 frames apart
- Caption appear: `easeOut(quad)` over 20 frames

## Narration Sync
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "So, injection molding, precision comes from the walls. The material just flows until it's constrained."

Segments: `part4_precision_tradeoff_002`, `part4_precision_tradeoff_003`

- **0:07** ("In 3D printing"): Split screen appears, both sides begin building
- **0:10** ("machine must know exactly"): Left side — nozzle depositing, coordinate grid brightening
- **0:15** ("every single point"): Left side — coordinate labels appearing at deposited points
- **0:20** ("extremely precise"): Left side fully built, grid prominent
- **0:21** ("injection molding"): Focus shifts right — liquid begins flowing
- **0:23** ("material just flows"): Liquid spreading chaotically
- **0:25** ("until it's constrained"): Liquid hits walls, walls glow amber, shape constrained

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={601}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — 3D Printing */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="3D PRINTING" font="Inter" size={20}
          weight={700} color="#60A5FA" opacity={0.7}
          x={479} y={80} align="center" />
      </FadeIn>

      {/* Coordinate grid */}
      <Sequence from={15}>
        <StrokeDraw duration={40}>
          <CoordinateGrid x={140} y={180} width={320} height={320}
            spacing={40} color="#60A5FA" opacity={0.08} dashed />
        </StrokeDraw>
      </Sequence>

      {/* Nozzle and depositing */}
      <Sequence from={30}>
        <PrinterNozzle startX={240} startY={200}
          layers={DEPOSIT_LAYERS} pointSize={6}
          color="#60A5FA" depositRate={5} />
      </Sequence>

      {/* Coordinate labels */}
      <Sequence from={210}>
        {DEPOSIT_POINTS.map((pt, i) => (
          <Sequence from={i * 3} key={pt.id}>
            <FadeIn duration={10}>
              <Text text={`(${pt.x},${pt.y})`} font="JetBrains Mono" size={8}
                color="#60A5FA" opacity={0.4}
                x={pt.screenX} y={pt.screenY - 12} />
            </FadeIn>
          </Sequence>
        ))}
      </Sequence>

      {/* Caption */}
      <Sequence from={390}>
        <FadeIn duration={20}>
          <Text text="Every point must be specified" font="Inter" size={14}
            color="#60A5FA" opacity={0.5} x={479} y={950} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — Injection Molding */}
    <Panel x={962} width={958}>
      <FadeIn duration={15}>
        <Text text="INJECTION MOLDING" font="Inter" size={20}
          weight={700} color="#D9944A" opacity={0.7}
          x={479} y={80} align="center" />
      </FadeIn>

      {/* Mold walls */}
      <Sequence from={15}>
        <StrokeDraw duration={40}>
          <MoldWalls cx={479} cy={500} width={300} height={400}
            color="#D9944A" opacity={0.6} strokeWidth={4}
            internalShapes={WALL_SHAPES} />
        </StrokeDraw>
      </Sequence>

      {/* Liquid flow */}
      <Sequence from={210}>
        <LiquidFlow nozzleY={200} moldBounds={MOLD_BOUNDS}
          color="#A78BFA" opacity={0.4}
          flowDuration={120} wallGlowColor="#D9944A"
          wallGlowOnImpact={true} />
      </Sequence>

      {/* Caption */}
      <Sequence from={390}>
        <FadeIn duration={20}>
          <Text text="Walls do the precision work" font="Inter" size={14}
            color="#D9944A" opacity={0.5} x={479} y={950} align="center" />
        </FadeIn>
      </Sequence>
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_split",
  "splitPosition": 960,
  "leftPanel": {
    "header": "3D PRINTING",
    "headerColor": "#60A5FA",
    "elements": [
      { "type": "coordinate_grid", "spacing": 40, "color": "#60A5FA" },
      { "type": "printer_nozzle", "layers": 3, "pointsPerLayer": 8 },
      { "type": "coordinate_labels", "font": "JetBrains Mono", "size": 8 }
    ],
    "caption": "Every point must be specified",
    "thematicRole": "explicit_precision"
  },
  "rightPanel": {
    "header": "INJECTION MOLDING",
    "headerColor": "#D9944A",
    "elements": [
      { "type": "mold_walls", "strokeWidth": 4, "color": "#D9944A" },
      { "type": "liquid_flow", "color": "#A78BFA" },
      { "type": "wall_glow_on_impact", "glowColor": "#D9944A" }
    ],
    "caption": "Walls do the precision work",
    "thematicRole": "emergent_precision"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]
}
```

---
