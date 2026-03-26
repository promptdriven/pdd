[split:]

# Section 4.2: 3D Printer vs Injection Mold — Split Screen Comparison

**Tool:** Split
**Duration:** ~20s (602 frames @ 30fps)
**Timestamp:** 0:07 - 0:27

## Visual Description

A vertical split screen comparing two manufacturing paradigms that represent opposite approaches to precision.

**LEFT — "3D PRINTING":** A stylized top-down view of a 3D printer nozzle depositing material point-by-point. A coordinate grid overlays the scene, with each deposited point marked by a precise coordinate label (x: 12.4, y: 8.7, z: 0.3). The grid pulses with data — every single point must be specified. The visual is dense, meticulous, exhausting. A counter ticks up: "Points specified: 2,847 / 2,847". Label below: "Every point must be defined."

**RIGHT — "INJECTION MOLDING":** A cross-section of an injection mold. Liquid material flows freely — chaotic, organic paths rendered as bezier curves. But the liquid hits sharp rectangular walls and is forced into a precise shape. The walls glow with emphasis. The liquid doesn't need to be precise — the WALLS do the precision work. Label below: "The walls do the precision work."

The split holds across segments 002, 003, and 004. During seg 002, the left panel animates (3D printer focus). During seg 003, the right panel animates (injection mold focus). During seg 004 ("This maps directly to PDD"), both panels hold as the connection is stated.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — 3D Printing
- Header: "3D PRINTING" — Inter, 16px, bold, `#F59E0B` at 0.7, y: 50
- Coordinate grid: 40px spacing, `#F59E0B` at 0.08, covering 850×680px area
- Nozzle path: animated polyline, `#F59E0B` at 0.8, 2px stroke, dashed trail
- Deposited points: small circles (3px radius), `#F59E0B` at 0.6, appear along path
- Coordinate labels: JetBrains Mono, 8px, `#F59E0B` at 0.3, next to select points
  - Example labels: "(12.4, 8.7, 0.3)", "(12.5, 8.7, 0.3)", "(12.6, 8.7, 0.3)"
- Point counter: "Points specified: {n} / 2,847" — Inter, 12px, `#F59E0B` at 0.6, bottom
- Caption: "Every point must be defined." — Inter, 13px, `#F59E0B` at 0.5, y: 980

#### Right Panel — Injection Molding
- Header: "INJECTION MOLDING" — Inter, 16px, bold, `#2DD4BF` at 0.7, y: 50
- Mold walls: sharp rectangular outlines, `#2DD4BF` at 0.6, 3px stroke, defining a part shape
- Liquid flow: 8-10 bezier curves flowing from top injection point, `#8B5CF6` at 0.4, 1.5px stroke
  - Paths are organic, chaotic, but all terminate at walls
  - Liquid particles: small dots (2px) streaming along curves, `#8B5CF6` at 0.3
- Wall glow: `#2DD4BF` at 0.15, 8px radius glow on wall edges when liquid contacts
- Filled region: as liquid accumulates, a filled shape appears inside walls, `#8B5CF6` at 0.2
- Caption: "The walls do the precision work." — Inter, 13px, `#2DD4BF` at 0.5, y: 980

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in. Headers appear.
2. **Frame 15-60 (0.5-2s):** Left panel: coordinate grid fades in. Nozzle path begins drawing.
3. **Frame 60-240 (2-8s):** Left panel: nozzle deposits points one by one. Counter ticks up. Coordinate labels appear near active points. Dense, meticulous feel.
4. **Frame 240-300 (8-10s):** Left panel: counter reaches ~1,400. Caption appears. Grid feels exhaustingly detailed.
5. **Frame 300-360 (10-12s):** Right panel begins. Mold walls draw in with sharp strokes.
6. **Frame 360-480 (12-16s):** Right panel: liquid streams pour from injection point. Bezier curves animate. Liquid hits walls — wall glow activates on contact. Filled region builds.
7. **Frame 480-540 (16-18s):** Right panel: mold is full. Walls are emphasized. Caption appears.
8. **Frame 540-602 (18-20s):** Both panels hold. Visual contrast lands: dense coordinates vs simple walls.

### Typography
- Headers: Inter, 16px, bold (700), respective colors
- Coordinate labels: JetBrains Mono, 8px, `#F59E0B` at 0.3
- Point counter: Inter, 12px, `#F59E0B` at 0.6
- Captions: Inter, 13px, respective colors at 0.5

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Nozzle path draw: linear (steady mechanical motion)
- Point deposit: `easeOut(quad)` per point, 2-frame stagger
- Counter tick: linear count-up
- Mold walls draw: `easeOut(cubic)` over 30 frames (sharp, decisive)
- Liquid flow: `easeIn(quad)` — starts slow, accelerates
- Wall glow: `easeOut(quad)` on contact, 10 frames
- Captions: `easeOut(quad)` over 20 frames

## Narration Sync
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."
> "This maps directly to PDD."

Segments: `part4_precision_tradeoff_002`, `part4_precision_tradeoff_003`, `part4_precision_tradeoff_004`

- **6.84s** (seg 002): Split appears, left panel (3D printer) animating
- **13s**: Nozzle depositing points, coordinate labels visible
- **20.22s** (seg 002 ends): Left panel dense with points
- **20.54s** (seg 003): Right panel (injection mold) animating, liquid flowing
- **26.58s** (seg 003 ends): Mold filled, walls emphasized
- **26.80s** (seg 004): Both panels hold — "This maps directly to PDD"
- **29.40s** (seg 004 ends): Split fades out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={602}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left panel — 3D Printing */}
    <Panel x={0} width={958}>
      <FadeIn duration={15}>
        <Text text="3D PRINTING" font="Inter" size={16}
          weight={700} color="#F59E0B" opacity={0.7}
          x={479} y={50} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <CoordinateGrid spacing={40} color="#F59E0B" opacity={0.08}
          width={850} height={680} x={55} y={80} />
      </Sequence>
      <Sequence from={60}>
        <NozzlePath
          points={generatePrintPath(2847)}
          strokeColor="#F59E0B" strokeOpacity={0.8} strokeWidth={2}
          dotColor="#F59E0B" dotOpacity={0.6} dotRadius={3}
          labelFont="JetBrains Mono" labelSize={8}
          labelColor="#F59E0B" labelOpacity={0.3}
          animationDuration={240} />
      </Sequence>
      <Sequence from={240}>
        <CountUp from={0} to={2847} duration={300}
          prefix="Points specified: " suffix=" / 2,847"
          font="Inter" size={12} color="#F59E0B" opacity={0.6}
          x={479} y={800} align="center" />
      </Sequence>
      <Sequence from={240}>
        <FadeIn duration={20}>
          <Text text="Every point must be defined." font="Inter" size={13}
            color="#F59E0B" opacity={0.5} x={479} y={980} align="center" />
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
        <Text text="INJECTION MOLDING" font="Inter" size={16}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={479} y={50} align="center" />
      </FadeIn>
      <Sequence from={300}>
        <MoldWalls shape="part_cavity" color="#2DD4BF" opacity={0.6}
          strokeWidth={3} glowColor="#2DD4BF" glowOpacity={0.15}
          glowRadius={8} drawDuration={30} />
      </Sequence>
      <Sequence from={360}>
        <LiquidFlow
          injectionPoint={[479, 100]} wallBounds="part_cavity"
          curveCount={10} curveColor="#8B5CF6" curveOpacity={0.4}
          particleColor="#8B5CF6" particleOpacity={0.3}
          fillColor="#8B5CF6" fillOpacity={0.2}
          animationDuration={120} />
      </Sequence>
      <Sequence from={480}>
        <FadeIn duration={20}>
          <Text text="The walls do the precision work." font="Inter" size={13}
            color="#2DD4BF" opacity={0.5} x={479} y={980} align="center" />
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
    "headerColor": "#F59E0B",
    "content": "coordinate_grid_with_nozzle_path",
    "pointCount": 2847,
    "caption": "Every point must be defined.",
    "thematicRole": "exhaustive_specification"
  },
  "rightPanel": {
    "header": "INJECTION MOLDING",
    "headerColor": "#2DD4BF",
    "content": "mold_walls_with_liquid_flow",
    "wallCount": 6,
    "liquidCurves": 10,
    "caption": "The walls do the precision work.",
    "thematicRole": "wall_based_precision"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003", "part4_precision_tradeoff_004"]
}
```

---
