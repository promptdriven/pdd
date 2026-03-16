[split:]

# Section 4.1: 3D Printer vs Injection Mold Split

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:04 – 0:14

## Visual Description
A split-screen comparison contrasting two manufacturing approaches. The left panel shows a 3D printer nozzle depositing material point-by-point on a coordinate grid — each point explicitly specified, slow, tedious. The right panel shows an injection mold cavity where liquid pours in and flows chaotically until it contacts walls, which shape the output. The visual metaphor is immediate: explicit specification (3D printing) vs. constraint-driven shaping (injection molding). The divider pulses softly. Each side has a footer label summarizing the approach.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Vertical divider: 2px, `rgba(255,255,255,0.12)`, centered at x=960

### Chart/Visual Elements
- **Left Panel — 3D Printer (x: 0–958)**
  - Header: "3D Printing" — `#94A3B8`, 20px, centered at (480, 60)
  - Coordinate grid: 400×400px centered at (480, 400), faint white grid lines at 0.06 opacity, 50px spacing
  - Nozzle: Simplified printer head icon, 30×20px, `#6B7C93`, positioned above current deposit point
  - Deposit trail: Small circles (6px radius), `#EF4444` at 0.7 opacity, appearing sequentially at grid intersections
  - Coordinate labels: As each point deposits, a tiny label "(x, y)" appears briefly — `#EF4444` at 0.4 opacity, JetBrains Mono 10px
  - Footer label: "Every point specified" — `#EF4444`, 16px, bold, centered at (480, 720)

- **Right Panel — Injection Mold (x: 962–1920)**
  - Header: "Injection Molding" — `#94A3B8`, 20px, centered at (1440, 60)
  - Mold cavity: Curly-brace / wrench-shaped outline, thick walls (6px), `#D9944A` at 0.6 opacity, centered at (1440, 400), ~400×400px bounding box
  - Liquid flow: Particles (small circles 4px, `#4A90D9` at 0.5 opacity) pour from top-center nozzle, spread chaotically, then contact walls and settle
  - Wall glow: As liquid contacts each wall segment, the segment briefly pulses `#D9944A` at full opacity
  - Footer label: "Walls do the work" — `#D9944A`, 16px, bold, centered at (1440, 720)

### Animation Sequence
1. **Frame 0–20 (0–0.67s):** Vertical divider draws top-to-bottom. Both headers fade in. Grid and mold cavity wireframe appear simultaneously.
2. **Frame 20–90 (0.67–3.0s):** Left: Nozzle begins depositing points one-by-one. Each deposit: nozzle moves → pauses → dot appears → coordinate label blinks in/out. 10-frame cadence per point. Right: Liquid begins pouring — blue particles stream from top.
3. **Frame 90–180 (3.0–6.0s):** Left: 7 more points deposit along the shape outline. Progress is visible but slow — only ~40% of the target shape complete. Right: Liquid flow spreads, hitting first wall segments. Each wall glows on contact. Particles redirect and fill the cavity bottom.
4. **Frame 180–240 (6.0–8.0s):** Left: Nozzle continues, reaching 12 points total. Tedium is palpable. Right: Cavity filling rapidly. Walls constrain the flow — the shape emerges organically. Most of the cavity is filled.
5. **Frame 240–270 (8.0–9.0s):** Footer labels fade in simultaneously: "Every point specified" (left, red) and "Walls do the work" (right, amber).
6. **Frame 270–300 (9.0–10.0s):** Hold. Left panel shows incomplete shape (12 of ~30 points). Right panel shows the finished, wall-constrained shape fully filled.

### Typography
- Panel headers: Inter Medium, 20px, `#94A3B8`
- Coordinate labels: JetBrains Mono, 10px, `#EF4444` at 0.4 opacity
- Footer labels: Inter Bold, 16px, respective colors
- Nozzle indicator: No text, purely visual

### Easing
- Divider draw: `easeOutCubic`
- Point deposit: `spring({ damping: 20, stiffness: 200 })` (snappy pop-in)
- Nozzle movement: `easeInOutQuad`
- Liquid particle flow: linear with Perlin noise offset (organic spread)
- Wall glow pulse: `easeOutSine` (200ms on, 400ms fade)
- Footer fade: `easeOutQuad`

## Narration Sync
> "In 3D printing, there is no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Divider */}
    <Sequence from={0} durationInFrames={20}>
      <VerticalDivider x={960} color="rgba(255,255,255,0.12)" />
    </Sequence>

    {/* Left Panel — 3D Printer */}
    <AbsoluteFill style={{ clipPath: "inset(0 50% 0 0)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="3D Printing" color="#94A3B8" x={480} />
      </Sequence>
      <Sequence from={20} durationInFrames={220}>
        <CoordinateGrid x={480} y={400} size={400} />
        <PrinterNozzle
          points={printerPoints}
          cadence={10}
          dotColor="#EF4444"
          labelColor="#EF4444"
        />
      </Sequence>
      <Sequence from={240} durationInFrames={30}>
        <FadeIn>
          <FooterLabel text="Every point specified" color="#EF4444" x={480} />
        </FadeIn>
      </Sequence>
    </AbsoluteFill>

    {/* Right Panel — Injection Mold */}
    <AbsoluteFill style={{ clipPath: "inset(0 0 0 50%)" }}>
      <Sequence from={0} durationInFrames={20}>
        <PanelHeader text="Injection Molding" color="#94A3B8" x={1440} />
      </Sequence>
      <Sequence from={20} durationInFrames={220}>
        <MoldCavity x={1440} y={400} wallColor="#D9944A" />
        <LiquidFlow
          source={{ x: 1440, y: 180 }}
          particleColor="#4A90D9"
          wallGlowColor="#D9944A"
        />
      </Sequence>
      <Sequence from={240} durationInFrames={30}>
        <FadeIn>
          <FooterLabel text="Walls do the work" color="#D9944A" x={1440} />
        </FadeIn>
      </Sequence>
    </AbsoluteFill>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "leftPanel": {
    "title": "3D Printing",
    "footerLabel": "Every point specified",
    "color": "#EF4444",
    "printerPoints": [
      { "x": 2, "y": 8 }, { "x": 3, "y": 7 }, { "x": 4, "y": 7 },
      { "x": 5, "y": 6 }, { "x": 5, "y": 5 }, { "x": 5, "y": 4 },
      { "x": 4, "y": 4 }, { "x": 3, "y": 4 }, { "x": 3, "y": 3 },
      { "x": 3, "y": 2 }, { "x": 4, "y": 1 }, { "x": 5, "y": 1 }
    ],
    "gridSize": 400,
    "gridSpacing": 50
  },
  "rightPanel": {
    "title": "Injection Molding",
    "footerLabel": "Walls do the work",
    "color": "#D9944A",
    "cavityShape": "curly-brace",
    "wallThickness": 6
  }
}
```

---
