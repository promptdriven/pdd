[Remotion]

# Section 0.2: Zoom Out — Accumulated Patches

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:05 - 0:11

## Visual Description
An animated zoom-out that reveals the hidden cost of patching. The view starts tight on a single code diff (green/red highlighted lines) — the same edit we just saw. Then the virtual camera pulls back smoothly to reveal this diff is one of hundreds visible in a massive file tree. As the zoom continues, more files appear — each showing small colored diff markers (green insertions, red deletions, amber TODO highlights). The final wide shot shows an overwhelming mosaic of patched files stretching across the full canvas, with a subtle counter in the bottom-right tallying total patches (climbing rapidly from 1 to 2,847). The visual weight makes the accumulation feel oppressive.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0D1117 (GitHub dark theme)
- Grid lines: subtle #1B2028 horizontal rules between file rows

### Chart/Visual Elements
- **Single diff block (center start):** 240x160px, border-radius 6px, background #161B22
  - Green lines (#2EA04370, 3-4 lines), red lines (#F8514970, 2 lines)
  - Filename label above: `src/utils/parser.ts` in monospace
- **File tree nodes:** 80x50px rectangles with colored diff indicators
  - Green dot: insertion-heavy file
  - Red dot: deletion-heavy file
  - Amber dot: TODO/FIXME markers
- **Patch counter (bottom-right):** monospace digits, color #8B949E, counting up
- **Connecting lines:** faint #30363D lines between files suggesting dependency graph

### Animation Sequence
1. **Frame 0-30 (0-1s):** Tight view on single diff block, slight pulse glow on green lines
2. **Frame 30-90 (1-3s):** Smooth zoom-out — camera scale goes from 4x to 1x, revealing surrounding files fading in from opacity 0 → 1 as they enter view. Files appear in concentric rings outward.
3. **Frame 90-120 (3-4s):** Final zoom position reached. Patch counter begins rapid climb (1 → 2,847). Diff markers across all files pulse subtly in a wave pattern radiating from center.
4. **Frame 120-150 (4-5s):** Hold on wide shot. Counter lands on 2,847. Slight vignette darkens edges, drawing focus to the overwhelming volume.

### Typography
- Filename labels: `JetBrains Mono`, 11px, #8B949E, opacity 0.7
- Patch counter: `JetBrains Mono`, 28px, #8B949E → #E6EDF3 on final number
- Counter label: `JetBrains Mono`, 12px, #484F58, text "patches across 312 files"

### Easing
- Zoom-out: `easeInOutCubic`
- File node fade-in: `easeOutQuad` (staggered 20ms per ring)
- Counter climb: `easeOutExpo` (fast start, decelerates)

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ background: '#0D1117' }}>
    <Sequence from={0} durationInFrames={30}>
      <DiffBlock file="src/utils/parser.ts" insertions={4} deletions={2} />
    </Sequence>
    <Sequence from={30} durationInFrames={90}>
      <ZoomOutCamera from={4} to={1} easing={easeInOutCubic}>
        <FileTreeMosaic files={patchedFiles} />
      </ZoomOutCamera>
    </Sequence>
    <Sequence from={90} durationInFrames={60}>
      <PatchCounter from={1} to={2847} />
      <WavePulse origin="center" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "data_visualization",
  "totalPatches": 2847,
  "totalFiles": 312,
  "diffBreakdown": {
    "insertionHeavy": 187,
    "deletionHeavy": 62,
    "todoMarkers": 63
  },
  "centerFile": "src/utils/parser.ts",
  "zoomRange": { "start": 4.0, "end": 1.0 }
}
```
