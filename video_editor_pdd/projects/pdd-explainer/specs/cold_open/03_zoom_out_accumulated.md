[Remotion]

# Section 0.3: Zoom Out Accumulated — The Weight of Careful Repair

**Tool:** Remotion
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 0:08 - 0:15

## Visual Description

The split screen from scene 0.1 transforms via a synchronized zoom-out on both panels. LEFT: the single clean AI edit pulls back to reveal it was one patch among thousands — a sprawling codebase fills the screen with file trees, diff markers in red and green, scattered `// TODO` and `// HACK` comments floating as semi-transparent overlays. A counter ticks up: "1,247 patches". RIGHT: the grandmother's neatly darned sock pulls back to reveal an open dresser drawer overflowing with carefully mended garments — socks, shirts, trousers, each with visible repair stitches. A matching counter: "47 mended garments". The split divider remains. Both sides groan under the accumulated weight of diligent repair work.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117` (LEFT), `#1A1410` (RIGHT, warm dark)
- Split divider: vertical at x: 960, `#334155` at 0.4, 2px

### Chart/Visual Elements

**LEFT Panel — Codebase Sprawl**
- Base: dark IDE grid of code file rectangles, 80+ blocks arranged in a dependency graph layout
- Each block: 40x24px, `#161B22` fill, `#30363D` border at 0.5
- Diff markers: small red (`#F85149`) and green (`#3FB950`) bars on ~60% of blocks
- Floating comments: `// TODO: refactor`, `// HACK`, `// fixed null case`, `// workaround for #412` — Inter 11px, `#8B949E` at 0.35, scattered at random positions
- Patch counter: bottom-left at (24, 1040), Inter Bold 28px, `#F85149` at 0.85
- Subtle red glow behind the mass: radial gradient `#F85149` at 0.04

**RIGHT Panel — Mended Garments**
- Illustrated dresser drawer (top-down view), warm wood tone `#8B6D4B`
- Garments: stylized fabric rectangles with visible cross-stitch repair marks
- Each garment: muted colors (cream, navy, gray, brown) with amber `#D9944A` stitch lines
- Garment counter: bottom-right at (1880, 1040), Inter Bold 28px, `#D9944A` at 0.85

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Hold on the split screen from previous scene. The completed tasks are visible.
2. **Frame 10-90 (0.33-3s):** Simultaneous zoom-out on both panels. Scale: 1.0 → 0.15. The single edit/sock shrinks as the full picture emerges. Code blocks and garments fade in progressively from center outward.
3. **Frame 90-140 (3-4.67s):** Zoom settles. Floating TODO comments drift in from edges with staggered delays (50ms apart). Diff markers pulse once. Stitch lines on garments draw in.
4. **Frame 140-180 (4.67-6s):** Counters animate: LEFT counts from 0 → 1,247 (ease-out), RIGHT counts from 0 → 47 (ease-out). Both reach final values at the same frame.
5. **Frame 180-210 (6-7s):** Hold. A slow, heavy pulse on both panels — subtle brightness oscillation (±0.02) conveying weight.

### Typography
- Floating comments: Inter Regular, 11px, `#8B949E` at 0.35
- Patch counter: Inter Bold, 28px, `#F85149` at 0.85
- Garment counter: Inter Bold, 28px, `#D9944A` at 0.85
- Counter suffix: "patches" / "mended garments" — Inter Regular, 16px, same color at 0.6

### Easing
- Zoom out: `easeInOut(cubic)` — smooth deceleration
- Code block fade-in: `easeOut(quad)` — staggered, 2ms delay per block from center
- Counter tick-up: `easeOut(expo)` — fast start, slow settle on final number
- Brightness pulse: `sine` — gentle oscillation

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

| Segment ID | Text | Sync Point |
|---|---|---|
| `cold_open_003` | "But here's what your great-grandmother figured out..." | Frame 10 — zoom-out begins |
| `cold_open_004` | "...sixty years ago." | Frame 140 — counters start, full weight visible |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  <SplitScreen dividerX={960}>
    {/* LEFT: Codebase sprawl */}
    <LeftPanel>
      <ZoomOut from={1.0} to={0.15} startFrame={10} duration={80}>
        <CodebaseGrid blocks={codeBlocks} diffMarkers={true} />
      </ZoomOut>
      <Sequence from={90} durationInFrames={50}>
        <StaggeredFadeIn items={todoComments} delayMs={50} />
      </Sequence>
      <Sequence from={140} durationInFrames={40}>
        <AnimatedCounter from={0} to={1247} suffix=" patches" />
      </Sequence>
    </LeftPanel>

    {/* RIGHT: Mended garments */}
    <RightPanel>
      <ZoomOut from={1.0} to={0.15} startFrame={10} duration={80}>
        <DresserDrawer garments={mendedGarments} />
      </ZoomOut>
      <Sequence from={140} durationInFrames={40}>
        <AnimatedCounter from={0} to={47} suffix=" mended garments" />
      </Sequence>
    </RightPanel>
  </SplitScreen>

  {/* Weight pulse */}
  <Sequence from={180} durationInFrames={30}>
    <BrightnessPulse amplitude={0.02} frequency={1} />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_infographic",
  "layout": "split_screen",
  "left": {
    "label": "Codebase Patches",
    "blockCount": 80,
    "diffMarkerPercent": 60,
    "floatingComments": [
      "// TODO: refactor",
      "// HACK",
      "// fixed null case",
      "// workaround for #412",
      "// legacy — do not touch",
      "// temporary fix 2023-04"
    ],
    "counter": { "from": 0, "to": 1247, "suffix": " patches", "color": "#F85149" }
  },
  "right": {
    "label": "Mended Garments",
    "garmentCount": 47,
    "garmentTypes": ["sock", "shirt", "trouser", "sock", "sweater"],
    "counter": { "from": 0, "to": 47, "suffix": " mended garments", "color": "#D9944A" }
  },
  "zoom": { "from": 1.0, "to": 0.15, "startFrame": 10, "durationFrames": 80 },
  "narrationSegments": ["cold_open_003", "cold_open_004"]
}
```
