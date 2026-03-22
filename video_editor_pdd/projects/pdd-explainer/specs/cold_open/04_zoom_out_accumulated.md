[Remotion]

# Section 0.2: Zoom Out — Accumulated Patches Reveal

**Tool:** Remotion
**Duration:** ~5.5s (165 frames @ 30fps)
**Timestamp:** 0:06 - 0:11

## Visual Description

The split screen from the previous spec holds, but now both sides zoom out to reveal the accumulated weight of all that careful repair work.

**LEFT panel — Code:** The single clean edit from the developer shot pulls back to reveal it's one patch among hundreds. The codebase expands outward — files multiply, diff markers appear, `// TODO` comments scatter across the surface, `// HACK` and `// temporary fix` labels glow faintly. The single edit that looked so satisfying is now a tiny green dot in a sea of amber/red patches. A counter ticks upward: "patches: 1 → 47 → 312 → 1,847".

**RIGHT panel — Socks:** The grandmother's single repaired sock pulls back to reveal an open drawer full of carefully mended garments — socks, shirts, trousers — each with visible repair marks. The mending is skilled but the sheer quantity is overwhelming. This panel is a static illustration (Remotion-drawn) rather than Veo, matching the stylized zoom-out.

The zoom-out is smooth and continuous. Both panels expand at the same rate. The split divider remains at center. The visual argument: both are skilled at repair, but the accumulation is the real story.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind panels)
- Split line: 2px vertical divider at x: 960, color `#1E293B` at 0.15

### Chart/Visual Elements

#### Left Panel — Codebase Zoom Out
- Initial state: single highlighted code edit (green glow `#5AAA6E` at 0.3) centered in panel
- Zoom-out reveals grid of code file blocks:
  - Each file: 40x28px rounded rect, `#1E293B` fill, `#334155` 1px border at 0.3
  - Patch markers on files: small colored dots
    - Green dots (recent AI edits): `#5AAA6E` at 0.5
    - Amber dots (older patches): `#D9944A` at 0.4
    - Red dots (problematic patches): `#E74C3C` at 0.3
  - Scattered TODO labels: JetBrains Mono, 6px, `#D9944A` at 0.25, rotated ±5°
  - Scattered HACK labels: JetBrains Mono, 6px, `#E74C3C` at 0.2, rotated ±3°
- Patch counter: Inter, 16px, bold (700), `#94A3B8` at 0.5, bottom-left of panel
  - Ticks: "1" → "47" → "312" → "1,847" over 3s

#### Right Panel — Mended Garments Drawer
- Initial state: single repaired sock centered (stylized illustration)
- Zoom-out reveals open wooden drawer (warm brown `#8B6F47` border lines)
- Drawer contents: 12-16 garment shapes arranged in rows
  - Socks (6): dark ovals with visible cross-hatch repair marks in lighter thread
  - Shirts (4): folded rectangles with patch squares in contrasting colors
  - Trousers (3): folded shapes with knee-area patches
  - Each repair mark: thin lines in `#D9944A` at 0.3 (the thread color)
- Warm amber wash over entire panel: `#D9944A` at 0.03

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen holds from previous spec. Both panels show completed single tasks.
2. **Frame 15-90 (0.5-3s):** Smooth zoom-out on both panels simultaneously. LEFT: code files multiply outward from center. RIGHT: drawer opens and garments appear. Scale factor: 1.0 → 0.15 (revealing ~7x more content).
3. **Frame 90-120 (3-4s):** Zoom settles. Patch counter on LEFT ticks rapidly: 1 → 47 → 312 → 1,847. TODO/HACK labels fade in scattered across the code grid.
4. **Frame 120-150 (4-5s):** Hold. Both sides fully revealed. The weight of accumulation is visible.
5. **Frame 150-165 (5-5.5s):** Brief hold before transition to next beat.

### Typography
- Patch counter: Inter, 16px, bold (700), `#94A3B8` at 0.5
- TODO labels: JetBrains Mono, 6px, `#D9944A` at 0.25
- HACK labels: JetBrains Mono, 6px, `#E74C3C` at 0.2

### Easing
- Zoom-out scale: `easeInOut(cubic)` over 75 frames
- File block appearance: `easeOut(quad)` staggered from center outward, 2-frame delay per ring
- Patch counter tick: `easeOut(expo)` with 15-frame intervals
- TODO/HACK label fade: `easeOut(quad)` over 10 frames, staggered randomly

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

Segment: `cold_open_003`

- **5.82s** ("But here's what"): Zoom-out begins — both panels start expanding
- **8.00s** ("figured out"): Zoom-out complete — full accumulation visible
- **11.28s** ("sixty years ago"): Hold — the weight of the visual sinks in

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={165}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Code zoom out */}
    <Panel x={0} width={958}>
      <ZoomContainer from={1.0} to={0.15} duration={75} startFrame={15}>
        {/* Central highlighted edit */}
        <CodeEditHighlight color="#5AAA6E" opacity={0.3} />

        {/* Expanding grid of file blocks */}
        <Sequence from={15}>
          <CodeFileGrid
            count={200}
            blockSize={{ w: 40, h: 28 }}
            fill="#1E293B"
            border="#334155"
            patchColors={['#5AAA6E', '#D9944A', '#E74C3C']}
            staggerDelay={2}
          />
        </Sequence>

        {/* Scattered labels */}
        <Sequence from={90}>
          <ScatteredLabels
            labels={['// TODO', '// HACK', '// temporary fix', '// don\'t touch']}
            font="JetBrains Mono" size={6}
            colors={['#D9944A', '#E74C3C']}
            opacity={0.25}
            count={20}
          />
        </Sequence>
      </ZoomContainer>

      {/* Patch counter */}
      <Sequence from={90}>
        <AnimatedCounter
          values={[1, 47, 312, 1847]}
          prefix="patches: "
          font="Inter" size={16} weight={700}
          color="#94A3B8" opacity={0.5}
          x={40} y={1000}
          interval={15}
        />
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#1E293B" opacity={0.15} width={2} />

    {/* Right panel — Garment drawer zoom out */}
    <Panel x={962} width={958}>
      <ZoomContainer from={1.0} to={0.15} duration={75} startFrame={15}>
        <DarnedSock centerX={479} centerY={540} />

        <Sequence from={15}>
          <GarmentDrawer
            drawerColor="#8B6F47"
            garments={[
              { type: 'sock', count: 6 },
              { type: 'shirt', count: 4 },
              { type: 'trousers', count: 3 }
            ]}
            repairColor="#D9944A"
            repairOpacity={0.3}
          />
        </Sequence>
      </ZoomContainer>

      <ColorGrade color="#D9944A" opacity={0.03} />
    </Panel>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_infographic",
  "layout": "split_screen_zoom_out",
  "splitPosition": 960,
  "leftPanel": {
    "content": "code_accumulation_grid",
    "fileCount": 200,
    "patchCounter": {
      "values": [1, 47, 312, 1847],
      "label": "patches"
    },
    "scatteredLabels": ["// TODO", "// HACK", "// temporary fix", "// don't touch"],
    "colors": {
      "recentEdit": "#5AAA6E",
      "olderPatch": "#D9944A",
      "problematicPatch": "#E74C3C",
      "fileBlock": "#1E293B"
    }
  },
  "rightPanel": {
    "content": "garment_drawer_illustration",
    "garments": [
      { "type": "sock", "count": 6 },
      { "type": "shirt", "count": 4 },
      { "type": "trousers", "count": 3 }
    ],
    "repairColor": "#D9944A",
    "drawerColor": "#8B6F47"
  },
  "zoomFactor": { "from": 1.0, "to": 0.15 },
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_003"]
}
```

---
