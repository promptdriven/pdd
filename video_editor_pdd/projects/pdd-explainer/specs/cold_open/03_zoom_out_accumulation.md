[Remotion]

# Section 0.3: Zoom Out — Accumulated Patches

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 0:15 - 0:30

## Visual Description
The split screen from the previous scene holds, then both sides zoom out dramatically to reveal the accumulated weight of all that careful repair work.

**Left side:** The single clean code edit zooms out to reveal it is one of hundreds of patches scattered across a massive codebase. File tabs multiply across the top. The editor view pulls back to show a file tree with dozens of files — each with orange/amber diff markers. TODO comments (`// TODO: fix later`, `// HACK:`) appear scattered like lint. The green diff highlight from the previous scene becomes just one tiny speck in a sea of amber patches.

**Right side:** The grandmother's single darned sock zooms out to reveal an open drawer full of dozens of carefully mended garments — socks, shirts, trousers — each with visible stitch-grid patterns. The careful work is admirable but overwhelming.

The zoom-out is the key emotional beat: what felt satisfying close up looks exhausting from a distance.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Left `#1A1B26`, Right `#2D1F14`
- Grid lines: None
- Vertical divider: 2px, `#FFFFFF` at 30% opacity, X=960

### Chart/Visual Elements
- **Left Panel (Zoomed Out Codebase):**
  - File tree: 30+ file entries, monospace text `#94A3B8`, each with amber `#D9944A` diff indicator dot
  - Tab bar: 12+ tabs, most with modified indicator dots `#D9944A`
  - Minimap column (right edge of editor): dense amber/orange streaks showing patch locations
  - TODO comment highlights: `#EF4444` background tint on scattered lines
  - The original green diff from Scene 2: tiny 4px green dot at one file, barely visible
  - Floating labels (fade in late): "patch", "patch", "patch" in `#D9944A` at 40% opacity, scattered

- **Right Panel (Zoomed Out Drawer):**
  - Open drawer shape: dark wood rectangle `#3D2B1A` with shadow
  - 15-20 garment shapes: rounded rectangles in various warm muted tones (`#8B7355`, `#7A6B5A`, `#6B5B4A`, `#9C8B7A`)
  - Each garment has a visible stitch-grid overlay: thin `#C49A6C` crosshatch pattern at 30% opacity
  - Stacking: garments overlap slightly, arranged in a drawer-like grid

### Animation Sequence
1. **Frame 0-60 (0-2.0s):** Simultaneous zoom out on both panels. Scale: 1.0→0.15 (revealing the full scope). Smooth, slow, cinematic pull-back.
2. **Frame 60-120 (2.0-4.0s):** Left: file tree entries populate one by one (staggered, 3 frames apart), each with amber diff dot. Right: garment shapes fade in staggered (4 frames apart)
3. **Frame 120-180 (4.0-6.0s):** Left: TODO highlights flicker on across various files. Minimap amber streaks intensify. Right: stitch-grid overlays fade in on each garment
4. **Frame 180-240 (6.0-8.0s):** Hold on the full accumulated view. The weight is visible.
5. **Frame 240-310 (8.0-10.3s):** Narration: "But here's what your great-grandmother figured out sixty years ago." — subtle camera drift (2px lateral movement) to add life
6. **Frame 310-450 (10.3-15.0s):** Hold. Both panels at full zoomed-out state. The parallel is clear.

### Typography
- TODO comments: JetBrains Mono, 11px, `#EF4444`
- File tree entries: JetBrains Mono, 12px, `#94A3B8`
- Floating "patch" labels: Inter, 14px, `#D9944A` at 40% opacity

### Easing
- Zoom out: `easeInOut(cubic)` — slow start, smooth middle, gentle stop
- File tree stagger: `easeOut(quad)` per item
- Garment stagger: `easeOut(quad)` per item
- TODO highlight flicker: `step` with slight randomization
- Camera drift: `linear`

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Left Panel — Code Accumulation */}
  <ZoomOut from={1.0} to={0.15} durationInFrames={60}>
    <CodebaseOverview>
      <Sequence from={60}>
        <StaggeredFileTree
          files={fileList}
          diffColor="#D9944A"
          staggerFrames={3}
        />
      </Sequence>
      <Sequence from={120}>
        <TodoHighlights positions={todoPositions} color="#EF4444" />
        <Minimap streakColor="#D9944A" />
      </Sequence>
    </CodebaseOverview>
  </ZoomOut>

  {/* Vertical Divider */}
  <VerticalDivider x={960} color="#FFFFFF" opacity={0.3} />

  {/* Right Panel — Garment Drawer */}
  <ZoomOut from={1.0} to={0.15} durationInFrames={60}>
    <DrawerOverview background="#3D2B1A">
      <Sequence from={60}>
        <StaggeredGarments
          items={garmentList}
          staggerFrames={4}
        />
      </Sequence>
      <Sequence from={120}>
        <StitchGridOverlays color="#C49A6C" opacity={0.3} />
      </Sequence>
    </DrawerOverview>
  </ZoomOut>
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "fileCount": 32,
    "diffIndicatorColor": "#D9944A",
    "todoHighlightColor": "#EF4444",
    "minimapStreakColor": "#D9944A",
    "originalDiffColor": "#50C878",
    "zoomScale": { "from": 1.0, "to": 0.15 }
  },
  "rightPanel": {
    "garmentCount": 18,
    "garmentColors": ["#8B7355", "#7A6B5A", "#6B5B4A", "#9C8B7A"],
    "stitchGridColor": "#C49A6C",
    "stitchGridOpacity": 0.3,
    "drawerColor": "#3D2B1A"
  },
  "animation": {
    "zoomDuration": 60,
    "fileStagger": 3,
    "garmentStagger": 4
  }
}
```

---
