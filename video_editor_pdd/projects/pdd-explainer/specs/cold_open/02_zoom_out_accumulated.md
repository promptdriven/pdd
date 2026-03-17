[Remotion]

# Section 0.2: Zoom Out — Accumulated Weight

**Tool:** Remotion
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 0:08 - 0:15

## Visual Description

The split screen from the previous shot holds — then both panels simultaneously zoom out to reveal the accumulated weight of all that careful repair work.

LEFT panel: The single code edit expands to reveal a massive codebase. Hundreds of files appear, each bearing diff markers, TODO comments, patch annotations. A counter in the corner ticks upward: "patches: 1,247." The screen fills with colorful but chaotic code — inline comments like `// fixed null case`, `// workaround for #412`, `// temporary`, scattered across dozens of files. The single clean edit was just one drop in an ocean of maintenance.

RIGHT panel: The grandmother's single mended sock pulls back to reveal an open drawer containing dozens of carefully mended garments — socks with neat darning patches, shirts with re-sewn buttons, trousers with reinforced knees. A counter ticks: "mended: 47." Each item represents hours of patient labor.

The zoom-out is smooth and continuous, 3Blue1Brown style — the camera pulls back as new detail materializes at the edges. The counters tick at matching rates, reinforcing the parallel.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.12 (continues from 01)

### Chart/Visual Elements

#### Left Panel — Code Codebase (x: 0 to x: 958)
- Initial state: the single edited function from 01, centered
- Zoom reveals: 8x8 grid of code file tiles, each ~110x90px
- Each tile: dark background `#0F172A`, syntax-highlighted code snippets, 10px padding
- Diff markers: red/green vertical bars on left edge of ~60% of tiles
- TODO labels: scattered `// TODO` badges in `#EF4444` at 0.5, 8px Inter
- Patch counter: "patches: 1,247" — JetBrains Mono, 14px, `#4A90D9` at 0.6, bottom-left corner (40, 1020)
- Counter ticks from 1 → 1,247 over 4 seconds

#### Right Panel — Mended Garments (x: 962 to x: 1920)
- Initial state: the single darned sock from 01, centered
- Zoom reveals: open wooden drawer filled with mended items
- Items rendered as warm-toned rectangular shapes with visible stitch marks
- Stitch marks: thin crosshatch lines in `#D9944A` at 0.3 over each item
- Mended counter: "mended: 47" — Inter, 14px, `#D9944A` at 0.6, bottom-right corner (1860, 1020)
- Counter ticks from 1 → 47 over 4 seconds

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Hold on the completed split from 01. Both sides show their single finished repair.
2. **Frame 15-120 (0.5-4s):** Simultaneous zoom out on both panels. Scale transitions from 1.0 → 0.15. LEFT: code tiles materialize at the edges, diff markers and TODO labels appear. RIGHT: drawer opens, mended items revealed one by one.
3. **Frame 120-150 (4-5s):** Counters begin ticking. LEFT: patches counter climbs rapidly. RIGHT: mended counter climbs steadily.
4. **Frame 150-180 (5-6s):** Full zoom achieved. Both sides show the accumulated weight. Counters reach final values.
5. **Frame 180-210 (6-7s):** Hold. The contrast between a single repair and an ocean of repairs is stark.

### Typography
- Patch counter: JetBrains Mono, 14px, `#4A90D9` at 0.6
- Mended counter: Inter, 14px, `#D9944A` at 0.6
- TODO labels: Inter, 8px, `#EF4444` at 0.5
- Inline comments: JetBrains Mono, 7px, `#64748B` at 0.3

### Easing
- Zoom out: `easeInOut(cubic)` over 105 frames (smooth, continuous)
- Tile reveal: `easeOut(quad)` staggered, 3-frame offset per row
- Counter tick: `easeOut(expo)` (fast start, slows at end)
- TODO badge pop-in: `easeOut(back(1.3))` with 5-frame stagger

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

Segment: `cold_open_002`

- **0:08** ("But here's what"): Zoom begins, both sides pulling back
- **0:10** ("your great-grandmother"): Mended drawer visible, grandmother's accumulated work revealed
- **0:12** ("figured out"): Counters ticking, full scope visible
- **0:14** ("sixty years ago"): Hold on accumulated weight, both counters at final values

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Code zoom out */}
    <Panel x={0} width={958}>
      <ZoomOut startScale={1.0} endScale={0.15}
        startFrame={15} duration={105}>
        <CodeTileGrid
          rows={8} cols={8} tileSize={[110, 90]}
          tiles={codebaseTiles}
          diffMarkersPercent={0.6}
          todoLabels={todoPositions}
          revealStagger={3}
        />
      </ZoomOut>
      <Sequence from={120}>
        <AnimatedCounter
          start={1} end={1247}
          prefix="patches: " font="JetBrains Mono" size={14}
          color="#4A90D9" opacity={0.6}
          x={40} y={1020} duration={60}
        />
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.12} />

    {/* Right panel — Garment zoom out */}
    <Panel x={962} width={958}>
      <ZoomOut startScale={1.0} endScale={0.15}
        startFrame={15} duration={105}>
        <MendedDrawer
          items={mendedGarments}
          stitchColor="#D9944A" stitchOpacity={0.3}
          revealStagger={5}
        />
      </ZoomOut>
      <Sequence from={120}>
        <AnimatedCounter
          start={1} end={47}
          prefix="mended: " font="Inter" size={14}
          color="#D9944A" opacity={0.6}
          x={1860} y={1020} align="right" duration={60}
        />
      </Sequence>
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_zoom_split",
  "chartId": "accumulated_weight_reveal",
  "leftPanel": {
    "label": "Codebase",
    "gridSize": [8, 8],
    "tileSize": [110, 90],
    "diffMarkerPercent": 0.6,
    "counter": { "label": "patches", "finalValue": 1247 },
    "inlineComments": [
      "// fixed null case",
      "// workaround for #412",
      "// TODO: refactor",
      "// temporary fix (2019)",
      "// don't touch this",
      "// legacy"
    ]
  },
  "rightPanel": {
    "label": "Mended garments",
    "itemCount": 47,
    "counter": { "label": "mended", "finalValue": 47 },
    "itemTypes": ["socks", "shirts", "trousers"]
  },
  "zoomConfig": {
    "startScale": 1.0,
    "endScale": 0.15,
    "startFrame": 15,
    "duration": 105
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_002"]
}
```

---
