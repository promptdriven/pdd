[split:]

# Section 0.1: Split Screen Hook — Developer vs Grandmother

**Tool:** Split
**Duration:** ~11s (339 frames @ 30fps)
**Timestamp:** 0:00 - 0:11

## Visual Description

A vertical split screen that opens the entire video with a striking visual parallel. **LEFT:** A modern software developer at their keyboard, Cursor IDE visible, making a slick AI-assisted code edit. The edit lands cleanly — a single function patched with confidence. Then the camera zooms out to reveal the edit is one of thousands in a massive codebase riddled with diff markers, TODO comments, and accumulated patches. **RIGHT:** A 1950s great-grandmother carefully darning a wool sock by warm lamplight. The patch finishes neatly. Then the camera zooms out to reveal her drawer — dozens of carefully mended socks, shirts, and trousers. The accumulated weight of careful repair work.

The split holds as both sides show their accumulated burden. The parallel is unmistakable: modern AI-assisted coding is the same activity as hand-mending garments — skilled, careful, and ultimately futile at scale.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind both panels)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Developer + Codebase
- **Phase 1 (0-5.5s):** Veo clip `developer_ai_edit` — medium shot of developer at keyboard, Cursor IDE on screen, making an AI-assisted edit. Monitor glow lights the scene.
- **Phase 2 (5.5-11s):** Virtual camera zooms out. The single edit is revealed as one of thousands of patches in a massive codebase. Diff markers (`+`, `-`), `// TODO` comments, `// HACK` annotations, stacked file tabs. The IDE panel shrinks into a sea of patched files.

#### Right Panel — Grandmother + Mended Garments
- **Phase 1 (0-5.5s):** Veo clip `grandmother_darning` — warm-lit close-up of elderly hands darning a wool sock by lamplight. Thread pulled through neatly.
- **Phase 2 (5.5-11s):** Virtual camera zooms out. A drawer opens revealing dozens of carefully mended garments — socks, shirts, trousers — each with visible patches. The accumulated labor is palpable.

#### Panel Labels (subtle)
- LEFT: no label (the IDE is self-explanatory)
- RIGHT: no label (the domestic scene is self-explanatory)
- The visual parallel does the work — no text needed.

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Black screen. Split line fades in from center outward.
2. **Frame 15-82 (0.5-2.72s):** Both panels active. LEFT: developer making an edit. RIGHT: grandmother darning. Narration: "If you use Cursor or Claude Code or Copilot..."
3. **Frame 82-104 (2.72-3.46s):** Brief pause. Both tasks near completion.
4. **Frame 104-165 (3.46-5.50s):** Both complete their task simultaneously. Code edit lands cleanly. Sock patch finishes neatly. Narration: "...you're getting really good at this."
5. **Frame 165-175 (5.50-5.82s):** Brief pause before the reveal.
6. **Frame 175-339 (5.82-11.28s):** Zoom out on BOTH sides simultaneously. LEFT reveals massive codebase. RIGHT reveals drawer of mended garments. Split holds. Narration: "But here's what your great-grandmother figured out sixty years ago."

### Typography
- None — pure visual storytelling. The Veo clips and zoom-out animation carry the narrative.

### Easing
- Split line fade: `easeOut(quad)` over 15 frames
- Zoom-out (both panels): `easeInOut(cubic)` over 90 frames — slow, cinematic pull
- Task completion moments: natural timing from Veo clips

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this. But here's what your great-grandmother figured out sixty years ago."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0:00** ("If you use Cursor"): Split screen appears, both subjects working
- **0:03** ("you're getting really good"): Both tasks complete — satisfying moment
- **0:06** ("But here's what"): Zoom out begins on both panels
- **0:09** ("sixty years ago"): Full accumulation visible on both sides, split holds

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={339}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      {/* Phase 1: close-up edit */}
      <Sequence from={0} durationInFrames={175}>
        <VeoClip clipId="developer_ai_edit"
          src="/clips/developer_ai_edit.mp4" fit="cover" />
      </Sequence>

      {/* Phase 2: zoom out to codebase */}
      <Sequence from={175}>
        <ZoomOut from={1.0} to={0.35} duration={90} easing="easeInOut(cubic)">
          <CodebaseReveal
            patches={["// TODO: refactor", "// HACK", "// temporary fix"]}
            diffMarkers={true}
            fileCount={47}
            font="JetBrains Mono" size={9} color="#94A3B8" />
        </ZoomOut>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
      </FadeIn>
    </Sequence>

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      {/* Phase 1: close-up darning */}
      <Sequence from={0} durationInFrames={175}>
        <VeoClip clipId="grandmother_darning"
          src="/clips/grandmother_darning.mp4" fit="cover" />
      </Sequence>

      {/* Phase 2: zoom out to mended garments */}
      <Sequence from={175}>
        <ZoomOut from={1.0} to={0.35} duration={90} easing="easeInOut(cubic)">
          <MendedGarmentsReveal
            items={["socks", "shirts", "trousers"]}
            patchCount={24}
            drawerOpen={true} />
        </ZoomOut>
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
    "content": "veo_clip_then_zoom_out",
    "clipId": "developer_ai_edit",
    "zoomOutReveals": "massive_codebase_with_patches",
    "thematicRole": "modern_developer_patching"
  },
  "rightPanel": {
    "content": "veo_clip_then_zoom_out",
    "clipId": "grandmother_darning",
    "zoomOutReveals": "drawer_of_mended_garments",
    "thematicRole": "grandmother_darning_socks"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]
}
```

---
