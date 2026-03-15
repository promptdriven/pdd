[split:]

# Section 4.2: 3D Printer vs Injection Mold — Split Comparison

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 18:34 - 18:42

## Visual Description
A split-screen comparison occupies the full canvas. The LEFT half shows a stylized 3D printer: a nozzle head moves along a precise coordinate grid, depositing material dot-by-dot along an exact path — every point explicitly specified. The RIGHT half shows an injection mold: liquid pours in from the top and flows freely, chaotically spreading until it contacts the walls, which constrain it into a clean shape. A vertical divider separates the halves. Labels identify each manufacturing approach. The contrast is immediate: explicit point-by-point specification vs. constraint-driven shaping.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None (each half has its own internal grid/visual treatment)

### Chart/Visual Elements
- **Vertical Divider:** 2px line at X=960, full height, `rgba(255,255,255,0.15)`
- **Left Panel — 3D Printer (X: 0-958)**
  - Label: "3D Printing" — `#94A3B8`, 22px, positioned at (240, 60)
  - Coordinate Grid: 20x12 dot grid, dots `rgba(255,255,255,0.08)`, 36px spacing, centered in panel
  - Nozzle Head: Small inverted triangle, 16px wide, `#4A90D9` at 0.8 opacity, positioned above the current deposit point
  - Deposited Material: Trail of filled dots, `#4A90D9` at 0.6 opacity, 6px diameter, tracing out a shape point-by-point
  - Path Guide: Faint dashed line connecting upcoming deposit points, `rgba(74,144,217,0.2)`, 1px
- **Right Panel — Injection Mold (X: 962-1920)**
  - Label: "Injection Molding" — `#94A3B8`, 22px, positioned at (1180, 60)
  - Mold Walls: Rectangular cavity outline, 340px wide x 240px tall, centered in panel, wall thickness 16px, `#D9944A` at 0.5 opacity
  - Nozzle Inlet: Small funnel at top-center of cavity, 40px wide, `#475569`
  - Liquid: Amorphous blob particles, blue-tinted `rgba(74,144,217,0.4)`, flowing from inlet and spreading chaotically until hitting walls
  - Wall Contact Glow: When liquid touches a wall, that wall segment briefly pulses to `#D9944A` at 0.8 opacity

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider line draws from top to bottom. Both labels fade in simultaneously
2. **Frame 20-40 (0.67-1.33s):** Left: coordinate grid dots fade in with subtle wave pattern. Right: mold walls draw in (stroke-dashoffset)
3. **Frame 40-150 (1.33-5.0s):** Left: nozzle head begins moving along grid, depositing dots one-by-one (12 frames per dot, ~9 dots total), dashed path guide visible ahead of nozzle. Right: liquid begins pouring from inlet, spreading organically downward and laterally
4. **Frame 100-180 (3.33-6.0s):** Right: liquid contacts left wall (wall pulses), then bottom (pulse), then right (pulse). Shape progressively defined by constraints
5. **Frame 150-200 (5.0-6.67s):** Left: nozzle continues depositing, shape ~60% complete. Right: liquid has filled cavity completely, surface settling
6. **Frame 200-240 (6.67-8.0s):** Both sides hold. Left panel gets a subtle label overlay: "Every point specified". Right panel: "Walls do the work". Labels fade in at 0.7 opacity, `#FFFFFF`, 18px, centered in each panel at Y=860

### Typography
- Panel Labels: Inter, 22px, semi-bold (600), `#94A3B8`
- Bottom Overlay Labels: Inter, 18px, medium (500), `#FFFFFF` at 0.7 opacity

### Easing
- Divider draw: `easeOut(cubic)`
- Grid fade-in: `easeOut(quad)`
- Nozzle movement (per step): `linear` (mechanical feel)
- Liquid spread: `easeOut(quad)` per expansion step
- Wall contact pulse: `easeInOut(sine)`
- Bottom labels fade: `easeOut(quad)`

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Divider */}
  <Sequence from={0} durationInFrames={20}>
    <VerticalDivider x={960} color="rgba(255,255,255,0.15)" />
  </Sequence>

  {/* Left Panel — 3D Printer */}
  <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
    <PanelLabel text="3D Printing" x={240} y={60} />
    <Sequence from={20} durationInFrames={20}>
      <CoordinateGrid cols={20} rows={12} spacing={36} dotColor="rgba(255,255,255,0.08)" />
    </Sequence>
    <Sequence from={40} durationInFrames={160}>
      <NozzleDepositor
        points={printerPath}
        dotColor="#4A90D9"
        nozzleColor="#4A90D9"
        framesPerDot={12}
      />
    </Sequence>
    <Sequence from={200}>
      <OverlayLabel text="Every point specified" y={860} />
    </Sequence>
  </AbsoluteFill>

  {/* Right Panel — Injection Mold */}
  <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
    <PanelLabel text="Injection Molding" x={1180} y={60} />
    <Sequence from={20} durationInFrames={20}>
      <MoldWalls width={340} height={240} wallThickness={16} color="#D9944A" />
    </Sequence>
    <Sequence from={40} durationInFrames={160}>
      <LiquidPour
        inletWidth={40}
        fillColor="rgba(74,144,217,0.4)"
        wallPulseColor="#D9944A"
        wallPulseOpacity={0.8}
      />
    </Sequence>
    <Sequence from={200}>
      <OverlayLabel text="Walls do the work" y={860} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "divider": {
    "x": 960,
    "color": "rgba(255,255,255,0.15)",
    "width": 2
  },
  "leftPanel": {
    "label": "3D Printing",
    "grid": { "cols": 20, "rows": 12, "spacing": 36, "dotColor": "rgba(255,255,255,0.08)" },
    "nozzle": { "width": 16, "color": "#4A90D9", "opacity": 0.8 },
    "depositDot": { "diameter": 6, "color": "#4A90D9", "opacity": 0.6 },
    "pathGuide": { "color": "rgba(74,144,217,0.2)", "dashPattern": "4 4" },
    "overlayLabel": "Every point specified"
  },
  "rightPanel": {
    "label": "Injection Molding",
    "mold": { "cavityWidth": 340, "cavityHeight": 240, "wallThickness": 16, "wallColor": "#D9944A", "wallOpacity": 0.5 },
    "inlet": { "width": 40, "color": "#475569" },
    "liquid": { "fillColor": "rgba(74,144,217,0.4)" },
    "wallPulse": { "color": "#D9944A", "peakOpacity": 0.8 },
    "overlayLabel": "Walls do the work"
  }
}
```

---
