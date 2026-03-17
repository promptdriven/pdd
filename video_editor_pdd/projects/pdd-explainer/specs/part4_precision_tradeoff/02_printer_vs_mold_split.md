[split:]

# Section 4.2: 3D Printer vs Injection Mold — Two Precision Paradigms

**Tool:** Split
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 18:34 - 18:54

## Visual Description

A vertical split screen contrasts two manufacturing paradigms. LEFT panel (labeled "3D PRINTING") shows a top-down view of a 3D printer nozzle depositing material point-by-point on a coordinate grid. Each deposited point requires an explicit coordinate — the grid is dense, and every intersection must be addressed. A counter shows "Points specified: N" incrementing rapidly. The nozzle moves methodically, leaving nothing to chance.

RIGHT panel (labeled "INJECTION MOLDING") shows a cross-section of a mold cavity. Liquid material flows in from a nozzle at the top and spreads freely — chaotically even — until it hits the amber wall boundaries. The walls do all the precision work. The liquid doesn't need coordinates; it just fills the space defined by constraints. A counter shows "Walls defined: 4" and stays constant.

The visual contrast is stark: the left side is exhaustive and effortful (specify everything), the right side is economical and elegant (specify only boundaries). Below the split, a single line emphasizes the point: "Precision through specification vs. precision through constraint."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x=960, color `#334155` at 0.25

### Chart/Visual Elements

#### Panel Headers
- LEFT: "3D PRINTING" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, letter-spacing 2px, centered at y: 40
- RIGHT: "INJECTION MOLDING" — Inter, 14px, semi-bold (600), `#D9944A` at 0.5, letter-spacing 2px, centered at y: 40

#### Left Panel — 3D Printer (x: 0 to x: 958)
- Background: `#0F172A`
- **Coordinate grid:** 20×20 grid, 36px spacing, centered in panel
  - Grid lines: `#1E293B` at 0.15, 1px
  - Intersection dots: `#334155` at 0.3, 3px — these are potential placement points
  - Active dots: `#4A90D9` (blue) at 0.8, 5px — deposited material
  - Nozzle icon: inverted triangle, `#E2E8F0` at 0.6, 12px, moves across grid
- **Counter:** "Points specified:" followed by incrementing number, Inter, 14px, `#94A3B8`, bottom of panel at y: 900
- **Annotation:** "Every point must be specified" — Inter, 11px, `#64748B` at 0.4, below counter

#### Right Panel — Injection Mold (x: 962 to x: 1920)
- Background: `#0A0F1A`
- **Mold cross-section:** 400×500px centered rectangle
  - Walls: 6px solid lines, `#D9944A` (amber) at 0.8
  - Wall labels: "WALL" in Inter, 8px, `#D9944A` at 0.4, rotated along each wall
  - Interior: initially empty, fills with `#4A90D9` (blue) at 0.2 as liquid flows in
  - Nozzle: top-center, funnel shape, `#94A3B8` at 0.5
- **Liquid fill animation:** Organic, fluid simulation — blue material enters from top, spreads chaotically, hits walls, fills cavity
- **Counter:** "Walls defined: 4" — Inter, 14px, `#D9944A`, bottom of panel at y: 900 (static)
- **Annotation:** "Precision comes from the walls" — Inter, 11px, `#D9944A` at 0.4, below counter

#### Bottom Callout (y: 980)
- "Precision through specification vs. precision through constraint" — Inter, 14px, `#E2E8F0` at 0.6
- "specification" in `#94A3B8`, "constraint" in `#D9944A`

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Split line draws. Panel headers fade in.
2. **Frame 20-60 (0.67-2s):** LEFT: Grid appears. Nozzle starts at top-left. RIGHT: Mold walls draw in.
3. **Frame 60-180 (2-6s):** LEFT: Nozzle traverses grid row by row. Each intersection it passes lights up blue. Counter increments: 1... 5... 20... 50... RIGHT: Liquid begins entering from nozzle. Flows downward, spreading freely.
4. **Frame 180-300 (6-10s):** LEFT: Nozzle at ~50% through grid. Counter: 100... 150... Still going. RIGHT: Liquid hits first wall, stops. Redirects. Flows along wall to next boundary. The constraint is visible.
5. **Frame 300-400 (10-13.3s):** LEFT: Nozzle at ~75%. Grid increasingly dense with blue dots. Counter: 200... 250... RIGHT: Mold cavity ~80% filled. Liquid conforms to wall shape perfectly. Still flowing.
6. **Frame 400-480 (13.3-16s):** LEFT: Grid fully populated. Counter: "400 points". Nozzle stops. RIGHT: Cavity fully filled. Clean shape. Counter still reads "Walls defined: 4".
7. **Frame 480-540 (16-18s):** Both panels hold. The contrast is stark: 400 specifications vs 4 constraints, same result.
8. **Frame 540-600 (18-20s):** Bottom callout fades in. "specification" and "constraint" highlighted in respective colors.

### Typography
- Panel headers: Inter, 14px, semi-bold (600), respective colors, letter-spacing 2px
- Counters: Inter, 14px, respective colors
- Annotations: Inter, 11px, respective colors at 0.4
- Callout: Inter, 14px, `#E2E8F0` at 0.6, keywords colored

### Easing
- Split line draw: `easeOut(cubic)` over 15 frames
- Nozzle movement: `linear` (mechanical, deliberate)
- Dot activation: `easeOut(quad)`, 3 frames scale-up
- Liquid flow: physics-based fluid simulation, `easeOut(cubic)` for leading edge
- Wall draw: `easeInOut(cubic)` over 30 frames
- Counter increment: `linear`
- Callout fade: `easeOut(quad)` over 20 frames

## Narration Sync
> "In 3D printing, there's no mold. The machine must know exactly where to place every single point of material. The specification must be extremely precise."
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

Segments: `part4_precision_tradeoff_002`, `part4_precision_tradeoff_003`

- **8.21s** ("In 3D printing, there's no mold"): Left panel grid appears, nozzle starts
- **11.8s** ("The machine must know exactly where to place"): Nozzle actively depositing, counter incrementing
- **17.06s** ("The specification must be extremely precise"): Grid densely populated
- **20.9s** ("injection molding, precision comes from the walls"): Right panel mold filling
- **24.3s** ("The material just flows until it's constrained"): Liquid hitting walls, conforming to shape

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — 3D Printing */}
    <Panel x={0} width={958}>
      <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
        <PanelHeader text="3D PRINTING" color="#94A3B8"
          opacity={0.5} letterSpacing={2} y={40} />

        <Sequence from={20}>
          <CoordinateGrid rows={20} cols={20} spacing={36}
            gridColor="#1E293B" dotColor="#334155"
            activeDotColor="#4A90D9" center={[480, 460]} />
          <PrinterNozzle
            grid={{ rows: 20, cols: 20, spacing: 36 }}
            center={[480, 460]}
            traverseDuration={380}
            nozzleColor="#E2E8F0" nozzleSize={12} />
        </Sequence>

        <Counter label="Points specified:" color="#94A3B8"
          font="Inter" size={14} position={[480, 900]}
          maxValue={400} duration={380} startFrame={60} />
        <Text text="Every point must be specified" font="Inter"
          size={11} color="#64748B" opacity={0.4}
          x={480} y={930} align="center" />
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
          <MoldCrossSection
            center={[480, 460]} size={[400, 500]}
            wallColor="#D9944A" wallWidth={6}
            wallDrawDuration={30} />
        </Sequence>

        <Sequence from={60}>
          <FluidFill
            moldBounds={{ x: 280, y: 210, w: 400, h: 500 }}
            fillColor="#4A90D9" fillOpacity={0.2}
            nozzlePosition={[480, 210]}
            fillDuration={340}
            wallCollisionBounce={true} />
        </Sequence>

        <Text text="Walls defined: 4" font="Inter" size={14}
          color="#D9944A" x={480} y={900} align="center" />
        <Text text="Precision comes from the walls" font="Inter"
          size={11} color="#D9944A" opacity={0.4}
          x={480} y={930} align="center" />
      </AbsoluteFill>
    </Panel>

    {/* Bottom callout */}
    <Sequence from={540}>
      <FadeIn duration={20}>
        <RichText x={960} y={980} align="center" font="Inter" size={14}
          color="#E2E8F0" opacity={0.6}>
          Precision through <Span color="#94A3B8">specification</Span>
          {' '}vs. precision through <Span color="#D9944A">constraint</Span>
        </RichText>
      </FadeIn>
    </Sequence>
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
    "concept": "Specify every point — exhaustive precision",
    "grid": { "rows": 20, "cols": 20, "totalPoints": 400 },
    "background": "#0F172A",
    "accentColor": "#94A3B8"
  },
  "rightPanel": {
    "label": "INJECTION MOLDING",
    "concept": "Define walls — constraint-based precision",
    "wallCount": 4,
    "background": "#0A0F1A",
    "accentColor": "#D9944A"
  },
  "callout": "Precision through specification vs. precision through constraint",
  "backgroundColor": "#000000",
  "narrationSegments": ["part4_precision_tradeoff_002", "part4_precision_tradeoff_003"]
}
```

---
