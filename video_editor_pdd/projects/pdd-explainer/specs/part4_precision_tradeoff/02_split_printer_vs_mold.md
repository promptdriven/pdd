[split:]

# Section 4.2: Split Screen — 3D Printer vs. Injection Mold

**Tool:** Split
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:08 - 0:24

## Visual Description

A split-screen composition that persists across three script beats (beats 1–3). This is the foundational metaphor for precision in PDD.

**LEFT PANEL:** A stylized Remotion animation of a 3D printer. A nozzle moves along precise coordinate paths, depositing material point-by-point on a grid. Each deposited point lights up on a visible coordinate grid overlay. The grid emphasizes that every single position must be explicitly specified. Clean, mechanical, precise — but laborious.

**RIGHT PANEL:** A stylized Remotion animation of an injection mold. Liquid material flows freely and chaotically through channels until it hits the walls of the mold cavity. The walls glow on contact — they're doing the precision work. The liquid doesn't need to be precise; the container is.

The split holds through "In 3D printing, there's no mold..." and "In injection molding, precision comes from the walls." The visual contrast makes the metaphor visceral: explicit specification vs. constraint-based shaping.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 40% opacity
- Background behind divider: `#0A0F1A`

### Panel Configuration

#### Left Panel — 3D Printer
- Background: `#0D1117` (slightly lighter navy)
- Coordinate grid: 40px spacing, `#1E293B` at 0.12
- Nozzle: White triangle/chevron shape, 20×12px, `#E2E8F0`
- Deposit trail: `#4A90D9` at 0.6, 6px dots at each grid intersection visited
- Path line: `#4A90D9` at 0.15, 1px, showing nozzle trajectory
- Grid coordinate labels (faint): `#64748B` at 0.2, 10px, at select intersections
- Header: "3D Printer" — Inter, 16px, semi-bold (600), `#94A3B8`, top-center of panel

#### Right Panel — Injection Mold
- Background: `#0D1117`
- Mold walls: `#D9944A` at 0.7, 4px solid lines forming a cavity shape (rounded rectangle with internal channels)
- Liquid flow: Animated particles/blobs, `#4A90D9` at 0.4, flowing from an injection point at top
- Wall glow on contact: `#D9944A` pulsing to 1.0 opacity where liquid meets wall, 8px glow radius
- Cavity interior: `#0F172A` — the void that shapes the output
- Header: "Injection Mold" — Inter, 16px, semi-bold (600), `#D9944A`, top-center of panel

### Animation Sequence
1. **Frame 0-30 (0-1s):** Split screen establishes from fade. Divider draws. Both panels reveal their backgrounds and grids/walls.
2. **Frame 30-150 (1-5s):** LEFT: Nozzle begins moving along a path, depositing dots at each grid point. Precise, deliberate, one-by-one. Coordinate grid becomes more prominent. RIGHT: Liquid begins flowing from injection point — a stream of animated particles.
3. **Frame 150-300 (5-10s):** LEFT: Nozzle continues. Grid fills further. The sheer number of specified points becomes apparent. RIGHT: Liquid hits walls. Wall segments glow amber on contact. Liquid fills the cavity, constrained by walls. Chaotic motion → perfect shape.
4. **Frame 300-420 (10-14s):** LEFT: Nozzle completes its path. All grid points filled. The fully specified object is visible. RIGHT: Mold cavity fully filled. Walls glowing. The shape is identical to the left — but achieved through constraint, not specification.
5. **Frame 420-480 (14-16s):** Hold. Both sides show the same output achieved through different means. Fade out.

### Typography
- Panel headers: Inter, 16px, semi-bold (600), respective colors
- Left grid labels: Inter, 10px, regular (400), `#64748B` at 0.2
- No other text — narration carries meaning

### Easing
- Divider fade-in: `easeOut(quad)` over 15 frames
- Panel fade-in: `easeOut(quad)` over 30 frames
- Nozzle movement: `linear` (mechanical, deliberate)
- Dot deposit: `easeOut(quad)` scale 0→1 over 4 frames
- Liquid flow: `easeIn(quad)` for initial flow, particles have slight randomness
- Wall glow: `easeOut(cubic)` over 10 frames per contact point
- Final fade: `easeIn(quad)` over 30 frames

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

Segment: `part4_precision_tradeoff_001` (from ~8s onward)

- **8.00s**: Split screen establishes — continuation of "subtle tradeoff" narration
- **12.00s**: LEFT nozzle depositing points — "must know exactly where to place every single point"
- **18.00s**: RIGHT liquid hitting walls — "precision comes from the walls"
- **24.00s**: Split fades out, transitioning to precision tradeoff curve

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.4}>
    {/* Left panel: 3D Printer */}
    <PanelLeft background="#0D1117">
      <Text text="3D Printer" font="Inter" size={16}
        weight={600} color="#94A3B8" y={30} align="center" />
      <CoordinateGrid spacing={40} color="#1E293B" opacity={0.12} />
      <Sequence from={30}>
        <PrinterNozzle
          path={printerPath}
          dotColor="#4A90D9" dotSize={6}
          nozzleColor="#E2E8F0"
          trailColor="#4A90D9" trailOpacity={0.15}
          depositDuration={390}
        />
      </Sequence>
      <Sequence from={150}>
        <FadeIn duration={30}>
          <GridLabels color="#64748B" opacity={0.2} size={10} />
        </FadeIn>
      </Sequence>
    </PanelLeft>

    {/* Right panel: Injection Mold */}
    <PanelRight background="#0D1117">
      <Text text="Injection Mold" font="Inter" size={16}
        weight={600} color="#D9944A" y={30} align="center" />
      <MoldWalls
        color="#D9944A" opacity={0.7} strokeWidth={4}
        shape="rounded_cavity_with_channels"
      />
      <Sequence from={30}>
        <LiquidFlow
          particleColor="#4A90D9" particleOpacity={0.4}
          injectionPoint={{ x: 470, y: 60 }}
          flowDuration={270}
        />
      </Sequence>
      <Sequence from={150}>
        <WallGlow
          color="#D9944A" glowRadius={8}
          triggerOnContact duration={10}
        />
      </Sequence>
    </PanelRight>
  </SplitScreen>

  {/* Fade out */}
  <Sequence from={420}>
    <FadeOut duration={60} />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.4 },
  "panels": {
    "left": {
      "label": "3D Printer",
      "animation": "printer_nozzle_grid",
      "accentColor": "#4A90D9",
      "description": "Nozzle deposits material point-by-point on coordinate grid"
    },
    "right": {
      "label": "Injection Mold",
      "animation": "liquid_flow_walls",
      "accentColor": "#D9944A",
      "description": "Liquid flows freely until walls constrain it into shape"
    }
  },
  "narrationSegments": ["part4_precision_tradeoff_001"],
  "durationSeconds": 16.0
}
```

---
