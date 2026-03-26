[split:]

# Section 1.11: Developer Darning Split — Cursor Dev vs Grandmother with Needle

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 7:21 - 7:29

## Visual Description

A vertical split screen that draws the final analogy. This is the emotional culmination — placing the developer with Cursor next to the grandmother with a darning needle. Both are working efficiently, skillfully. This is NOT dismissive of their tools — it's respectful of the skill while questioning the strategy.

**LEFT:** A developer working in Cursor or a code editor. Screen glowing, focused, productive. Code is being patched in real-time. The developer is competent, engaged.

**RIGHT:** A grandmother darning a wool sock with a needle. Warm lamplight, careful stitches, expert technique. She's skilled at her craft.

Both panels are lit warmly, treated with equal dignity. The split holds briefly, then zooms out on the developer's side to reveal the massive, tangled codebase surrounding their work — comments like "// don't touch this", "// legacy", "// temporary fix (2019)" visible in the code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind both panels)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Left Panel — Developer with Cursor
- Phase 1 (0-5s): Veo clip `developer_cursor_coding` — close-up of a developer at a modern setup. Code editor with dark theme visible. Focused, productive. Warm monitor glow.
- Phase 2 (5-8s): Virtual camera zooms out. The editor reveals a massive codebase. Legacy comments become visible in code: "// don't touch this", "// legacy", "// temporary fix (2019)". The tangled reality beyond the focused patch.

#### Right Panel — Grandmother Darning
- Phase 1 (0-8s): Veo clip `grandmother_darning_expert` — an elderly woman darning a wool sock under warm lamplight. Expert technique, careful stitches. A craft mastered over decades.

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split line fades in.
2. **Frame 15-150 (0.5-5s):** Both panels active. Developer coding. Grandmother darning. Both working with skill.
3. **Frame 150-210 (5-7s):** Left panel: virtual zoom out. The codebase expands. Legacy comments appear as overlaid text.
4. **Frame 210-240 (7-8s):** Hold. The developer is a tiny figure in a massive codebase. The grandmother is content with her single sock.

### Typography
- Legacy comments (overlaid on dev panel zoom-out): JetBrains Mono, 10px, `#94A3B8` at 0.4
  - "// don't touch this" at various positions
  - "// legacy" scattered
  - "// temporary fix (2019)" near bottom

### Easing
- Split line: `easeOut(quad)` over 15 frames
- Zoom out: `easeInOut(cubic)` over 60 frames — smooth dolly back
- Comment appear: `easeOut(quad)` staggered 10 frames apart

## Narration Sync
> "But they're still darning needles. Faster needles. AI-powered needles. But needles."

Segment: `part1_economics_033`

- **448.18s** ("But they're still darning needles"): Split screen appears
- **452s** ("Faster needles. AI-powered needles."): Developer zoom-out begins
- **455s** ("But needles."): Hold on zoomed-out view with legacy code visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      <VeoClip clipId="developer_cursor_coding"
        src="/clips/developer_cursor_coding.mp4" fit="cover" />

      {/* Zoom-out overlay with legacy comments */}
      <Sequence from={150}>
        <ZoomOut from={1.0} to={0.5} duration={60}>
          <CodeOverlay comments={[
            { text: "// don't touch this", x: 200, y: 300 },
            { text: "// legacy", x: 600, y: 150 },
            { text: "// temporary fix (2019)", x: 400, y: 700 },
            { text: "// TODO: refactor someday", x: 100, y: 500 },
            { text: "// no idea why this works", x: 700, y: 400 }
          ]} font="JetBrains Mono" size={10} color="#94A3B8" opacity={0.4} />
        </ZoomOut>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <FadeIn duration={15}>
      <SplitLine x={960} color="#334155" opacity={0.15} width={2} />
    </FadeIn>

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      <VeoClip clipId="grandmother_darning_expert"
        src="/clips/grandmother_darning_expert.mp4" fit="cover" />
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
    "content": "veo_clip_with_zoom_overlay",
    "clipId": "developer_cursor_coding",
    "zoomOut": { "startFrame": 150, "duration": 60, "from": 1.0, "to": 0.5 },
    "legacyComments": [
      "// don't touch this",
      "// legacy",
      "// temporary fix (2019)",
      "// TODO: refactor someday",
      "// no idea why this works"
    ],
    "thematicRole": "developer_patching"
  },
  "rightPanel": {
    "content": "veo_clip",
    "clipId": "grandmother_darning_expert",
    "thematicRole": "grandmother_darning"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["part1_economics_033"]
}
```

---
