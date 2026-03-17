[split:]

# Section 4.2: Printer vs Mold — Two Models of Precision

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 18:34 - 18:48

## Visual Description

A vertical split screen contrasts two manufacturing approaches to precision. LEFT panel (labeled "3D PRINTING") shows a printer nozzle depositing material point-by-point onto a coordinate grid. Each placed point lights up on the grid, emphasizing that every single position must be explicitly specified. A running counter shows "Points specified: 1… 47… 312… 1,847" — the number keeps climbing. RIGHT panel (labeled "INJECTION MOLDING") shows liquid material flowing freely and chaotically inside a mold cavity — swirling, splashing — until it hits the walls and takes shape. The walls glow. The liquid's exact path doesn't matter; only the walls do.

The contrast is stark: LEFT requires exhaustive specification of every point; RIGHT requires only the boundary definition. Both produce the same final shape.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "3D PRINTING" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.5, letter-spacing 2px, centered at y: 40
- RIGHT: "INJECTION MOLDING" — Inter, 14px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — 3D Printing (x: 0 to x: 958)
- Background: `#0F172A`
- **Coordinate grid:** 20x20 dot grid centered at (480, 450), dots `#1E293B` at 0.3, 3px each, spacing 18px
  - Grid represents the 2D plane the printer deposits onto
- **Printer nozzle:** Simplified triangular nozzle icon at top, `#4A90D9` at 0.6, 40x30px
  - Moves left-to-right, row-by-row across the grid
  - Small blue trail line from nozzle tip, 1px, `#4A90D9` at 0.3
- **Deposited points:** Each dot transitions from `#1E293B` to `#4A90D9` at 0.7 when the nozzle passes
  - Points light up sequentially, tracing out a shape (simplified bracket/part silhouette)
- **Point counter:** "Points specified: {N}" — JetBrains Mono, 14px, `#4A90D9` at 0.6, positioned at (480, 850)
  - Counts up from 0 as points are placed: 1, 5, 23, 78, 156, 312, 847, 1847
- **Subtext:** "Every point must be specified" — Inter, 11px, `#64748B` at 0.4, at y: 890

#### Right Panel — Injection Molding (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Mold cavity:** Simplified cross-section outline, same shape as the 3D-printed part
  - Walls: `#D9944A` at 0.5, 3px stroke, centered at (480, 450), ~280x350px
  - Interior: `#1E293B` at 0.1
- **Flowing liquid:** Animated particles/blobs flowing chaotically inside the cavity
  - Color: `#94A3B8` at 0.3, various sizes (4-10px), organic movement
  - Particles bounce off walls, swirl, gradually fill the space
  - The movement is deliberately chaotic — the liquid doesn't follow a precise path
- **Wall glow:** Once liquid settles, the walls pulse with `#D9944A` at 0.15, 30px Gaussian blur
  - The walls are what provide precision, not the liquid's path
- **Wall label:** "Walls do the precision work" — Inter, 11px, `#D9944A` at 0.5, at y: 890
- **Wall counter:** "Walls defined: 4" — JetBrains Mono, 14px, `#D9944A` at 0.6, at (480, 850)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-60 (0.67-2s):** LEFT: Coordinate grid fades in. Printer nozzle appears at top-left. RIGHT: Mold cavity outline draws itself.
3. **Frame 60-180 (2-6s):** LEFT: Nozzle traverses grid, depositing points one-by-one. Counter climbs rapidly. Each deposited point glows briefly. RIGHT: Liquid enters mold from top, flows chaotically, bounces off walls, gradually fills cavity.
4. **Frame 180-260 (6-8.67s):** LEFT: Shape becomes recognizable. Counter passes 1000. The exhaustive nature is visible. RIGHT: Liquid has settled into shape. Walls begin glowing — they constrained the liquid into the same shape.
5. **Frame 260-340 (8.67-11.33s):** Both shapes are now visible — same shape, different method. LEFT still depositing final points. RIGHT walls pulsing warmly.
6. **Frame 340-380 (11.33-12.67s):** Counter labels and subtexts appear. LEFT: "Points specified: 1,847" / RIGHT: "Walls defined: 4".
7. **Frame 380-420 (12.67-14s):** Hold. The contrast is the argument: 1,847 points vs. 4 walls, same result.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors at 0.5, letter-spacing 2px
- Point/wall counter: JetBrains Mono, 14px, respective colors at 0.6
- Subtexts: Inter, 11px, `#64748B` at 0.4
- Wall label: Inter, 11px, `#D9944A` at 0.5

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Grid fade: `easeOut(quad)` over 20 frames
- Nozzle movement: `linear` (constant scanning speed)
- Point deposit: `easeOut(quad)` brightness flash, 5 frames
- Liquid flow: physics-based (velocity, damping, wall collision)
- Wall glow pulse: `easeInOut(sine)` on 40-frame cycle
- Counter increment: `easeOut(quad)` per digit change

## Narration Sync
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

Segment: `part4_002`

- **18:34** ("In 3D printing, there's no mold"): Split screen appears, left panel grid and nozzle visible
- **18:38** ("every single point of material"): Nozzle actively depositing, counter climbing
- **18:42** ("In injection molding, precision comes from the walls"): Focus shifts to right panel, walls glowing
- **18:45** ("The material just flows until it's constrained"): Liquid settles into shape, wall glow pulses

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — 3D Printing */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="3D PRINTING" color="#4A90D9"
          opacity={0.5} letterSpacing={2} y={40} />

        <Sequence from={20}>
          <CoordinateGrid rows={20} cols={20} center={[480, 450]}
            dotSize={3} spacing={18}
            inactiveColor="#1E293B" activeColor="#4A90D9"
            inactiveOpacity={0.3} activeOpacity={0.7} />
        </Sequence>

        <Sequence from={60}>
          <PrinterNozzle startPos={[120, 100]}
            gridCenter={[480, 450]} scanSpeed={2}
            nozzleColor="#4A90D9" trailColor="#4A90D9"
            depositShape={partSilhouette}
            onDeposit={incrementCounter} />
        </Sequence>

        <PointCounter label="Points specified"
          font="JetBrains Mono" size={14}
          color="#4A90D9" opacity={0.6}
          position={[480, 850]} />

        <Sequence from={340}>
          <FadeIn duration={20}>
            <Text text="Every point must be specified"
              font="Inter" size={11} color="#64748B"
              opacity={0.4} x={480} y={890} align="center" />
          </FadeIn>
        </Sequence>
      </AbsoluteFill>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.25}
      drawDuration={15} />

    {/* Right panel — Injection Molding */}
    <Panel x={962} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
        <PanelHeader text="INJECTION MOLDING" color="#D9944A"
          opacity={0.5} letterSpacing={2} y={40} />

        <Sequence from={20}>
          <MoldCavity shape={partSilhouette}
            center={[480, 450]} size={[280, 350]}
            wallColor="#D9944A" wallOpacity={0.5} wallWidth={3}
            interiorColor="#1E293B" interiorOpacity={0.1}
            drawDuration={40} />
        </Sequence>

        <Sequence from={60}>
          <LiquidSimulation cavity={partSilhouette}
            particleCount={80} particleSizeRange={[4, 10]}
            color="#94A3B8" opacity={0.3}
            entryPoint={[480, 150]} flowDuration={120}
            damping={0.92} wallBounce={0.7} />
        </Sequence>

        <Sequence from={180}>
          <WallGlow shape={partSilhouette}
            color="#D9944A" opacity={0.15}
            blur={30} pulsePeriod={40} />
        </Sequence>

        <Sequence from={340}>
          <FadeIn duration={20}>
            <Text text="Walls defined: 4" font="JetBrains Mono"
              size={14} color="#D9944A" opacity={0.6}
              x={480} y={850} align="center" />
            <Text text="Walls do the precision work"
              font="Inter" size={11} color="#D9944A"
              opacity={0.5} x={480} y={890} align="center" />
          </FadeIn>
        </Sequence>
      </AbsoluteFill>
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
    "label": "3D PRINTING",
    "concept": "Every point must be explicitly specified — exhaustive precision",
    "finalCount": 1847,
    "counterLabel": "Points specified",
    "color": "#4A90D9",
    "background": "#0F172A"
  },
  "rightPanel": {
    "label": "INJECTION MOLDING",
    "concept": "Walls constrain the flow — precision from boundaries, not specification",
    "finalCount": 4,
    "counterLabel": "Walls defined",
    "color": "#D9944A",
    "background": "#0A0F1A"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part4_002"]
}
```

---
