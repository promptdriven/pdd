[Remotion]

# Section 0.2: Zoom Out — Accumulated Repair Work

**Tool:** Remotion **Duration:** ~6s (180 frames @ 30fps) **Timestamp:** 0:05 - 0:11

## Visual Description

The split screen from 01 is still held. Now both sides pull back in a smooth zoom-out, revealing the accumulated weight of careful repair work.

LEFT side zooms out from the single code edit to reveal a massive codebase. The clean file expands to show hundreds of files in a file tree — diff markers (red/green lines) scattered everywhere, `TODO` comments floating as subtle labels, `// temporary fix (2019)` annotations visible. The single AI-assisted edit is now a tiny green dot among thousands of patches, each marked with its own faint glow.

RIGHT side zooms out from the grandmother's hands to reveal her open drawer — dozens of carefully mended socks, shirts, and trousers, each with visible stitch lines. The mending work is beautiful but the volume is overwhelming. Stitch marks accumulate as small amber indicators.

Both sides animate in sync. The zoom-out uses the same easing. The message is clear: both the developer and the grandmother are excellent at repair — but the accumulation is the problem.

## Technical Specifications

### Canvas

- Resolution: 1920x1080 (16:9)
- Background: #0A0F1A (deep charcoal)
- Vertical divider: 1px solid rgba(255,255,255,0.2) at x=960

### Chart/Visual Elements

**Left Panel — Codebase Zoom-Out**

- Starting view: single file (from 01), scale 1.0
- Ending view: file tree with 200+ files, scale 0.15
- Diff markers: small rectangles, red #EF4444 and green #5AAA6E, 4×2px each, scattered across files
- TODO labels: monospace "TODO" in #FBBF24 at 50% opacity, 10px font, ~15 visible
- Comment annotations: "// temporary fix (2019)", "// don't touch", "// legacy" in #64748B, 9px font
- Original edit: pulses as a small green dot #5AAA6E, 6px diameter

**Right Panel — Drawer Reveal**

- Starting view: grandmother's hands close-up, scale 1.0
- Ending view: open wooden drawer, scale 0.3
- Mended items: 24 garments arranged in drawer, each with 1-3 visible stitch lines
- Stitch marks: short lines in #D4A043, 2px wide
- Drawer wood: #6B4226 with grain texture lines in #503018
- Warm light persists: radial gradient #D4A043 at 20% opacity

**Counters (subtle, bottom of each panel)**

- LEFT: "patches: 1,247" in monospace, #64748B, 11px, bottom-left at (40, 1040)
- RIGHT: "mended: 47" in serif, #8B7355, 11px, bottom-right at (1840, 1040)

### Animation Sequence

1. **Frame 0-15 (0-0.5s):** Hold from previous scene. Both panels static at full zoom.
2. **Frame 15-90 (0.5-3.0s):** Synchronized zoom-out on both panels. Scale 1.0 → 0.15 (left) / 1.0 → 0.3 (right). New elements fade in as they enter frame — diff markers, TODO labels, garments in drawer.
3. **Frame 90-120 (3.0-4.0s):** Counters fade in at bottom of each panel. Numbers count up rapidly: LEFT 0 → 1,247 / RIGHT 0 → 47.
4. **Frame 120-180 (4.0-6.0s):** Hold. Both panels show the full accumulated weight. Original edit pulses faintly on the left. Subtle breathing animation on counters (opacity 0.7 → 0.9 → 0.7).

### Typography

- Patch counter (left): `JetBrains Mono`, 11px, #64748B, opacity 0.8
- Mended counter (right): `Georgia`, 11px, #8B7355, opacity 0.8
- TODO labels: `JetBrains Mono`, 10px, #FBBF24, opacity 0.5
- Code comments: `JetBrains Mono`, 9px, #64748B, opacity 0.6

### Easing

- Zoom-out: `easeInOut(cubic)`
- Element fade-in (during zoom): `easeOut(quad)`
- Counter count-up: `easeOut(cubic)`
- Pulse animation: `easeInOut(sin)`

## Narration Sync

> "But here's what your great-grandmother figured out sixty years ago."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={180}>
  <SplitScreen dividerX={960}>
    <Sequence from={0} durationInFrames={180}>
      <ZoomOut startScale={1.0} endScale={0.15} startFrame={15} endFrame={90}>
        <CodebaseReveal
          fileCount={200}
          diffMarkers={{ red: "#EF4444", green: "#5AAA6E" }}
          todoLabels={15}
          commentAnnotations={["// temporary fix (2019)", "// don't touch", "// legacy"]}
        />
      </ZoomOut>
      <Sequence from={90} durationInFrames={30}>
        <AnimatedCounter label="patches" endValue={1247} color="#64748B" />
      </Sequence>
    </Sequence>
    <Sequence from={0} durationInFrames={180}>
      <ZoomOut startScale={1.0} endScale={0.3} startFrame={15} endFrame={90}>
        <DrawerReveal garmentCount={24} stitchColor="#D4A043" />
      </ZoomOut>
      <Sequence from={90} durationInFrames={30}>
        <AnimatedCounter label="mended" endValue={47} color="#8B7355" />
      </Sequence>
    </Sequence>
  </SplitScreen>
</Sequence>
```

## Data Points

```json
{
  "layout": {
    "splitX": 960,
    "divider": { "width": 1, "color": "rgba(255,255,255,0.2)" }
  },
  "leftPanel": {
    "zoom": { "start": 1.0, "end": 0.15, "startFrame": 15, "endFrame": 90 },
    "fileCount": 200,
    "diffMarkers": {
      "colors": { "red": "#EF4444", "green": "#5AAA6E" },
      "size": [4, 2]
    },
    "todoLabels": {
      "count": 15,
      "color": "#FBBF24",
      "opacity": 0.5,
      "fontSize": 10
    },
    "comments": [
      "// temporary fix (2019)",
      "// don't touch",
      "// legacy"
    ],
    "counter": {
      "label": "patches",
      "endValue": 1247,
      "position": [40, 1040],
      "color": "#64748B"
    }
  },
  "rightPanel": {
    "zoom": { "start": 1.0, "end": 0.3, "startFrame": 15, "endFrame": 90 },
    "garments": {
      "count": 24,
      "stitchesPerGarment": [1, 3],
      "stitchColor": "#D4A043"
    },
    "drawer": {
      "woodColor": "#6B4226",
      "grainColor": "#503018"
    },
    "counter": {
      "label": "mended",
      "endValue": 47,
      "position": [1840, 1040],
      "color": "#8B7355"
    }
  },
  "narrationSegments": ["cold_open_003"],
  "narrationTimingSeconds": { "start": 5.82, "end": 11.28 }
}
```

---