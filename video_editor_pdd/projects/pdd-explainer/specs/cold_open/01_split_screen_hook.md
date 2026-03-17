[split:]

# Section 0.1: Split Screen Hook — Developer Meets Grandmother

**Tool:** Split
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

The video opens cold on a vertical split screen. LEFT panel: a modern developer at a keyboard, Cursor IDE visible, making a slick AI-assisted code edit. The interface is real — syntax-highlighted code, a glowing cursor, an inline diff appearing. RIGHT panel: a 1950s great-grandmother carefully darning a wool sock by lamplight. Warm amber tones, weathered hands, a wooden darning egg.

Both subjects complete their task simultaneously. The code edit lands cleanly — green diff merged, cursor blinks satisfied. The sock patch finishes neatly — needle pulls through the final stitch, thread snipped. The visual parallel is immediate and visceral: these two people are doing the same thing, separated by seventy years.

The split is clean — a thin vertical divider, no fancy transitions. Each side embeds a Veo clip for live-action feel, with the split framing controlled by Remotion. The mood is respectful of both crafts — neither is diminished. Both are skilled. Both are meticulous.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.12

### Chart/Visual Elements

#### Panel Headers
- LEFT: "2025" — Inter, 11px, semi-bold (600), `#4A90D9` at 0.25, letter-spacing 3px, centered at y: 36
- RIGHT: "1955" — Inter, 11px, semi-bold (600), `#D9944A` at 0.25, letter-spacing 3px, centered at y: 36

#### Left Panel — Developer (x: 0 to x: 958)
- Background: cool blue monitor glow over Veo clip
- Veo clip: developer at desk, Cursor IDE on screen, making an AI-assisted edit — inline diff appears, code merges cleanly
- Color grade overlay: `#4A90D9` at 0.02, cool blue tone
- Subtle vignette: radial gradient, edges darkened to `#000510` at 0.20

#### Right Panel — Grandmother (x: 962 to x: 1920)
- Background: warm amber lamplight over Veo clip
- Veo clip: elderly woman darning a wool sock by lamplight — careful stitches, wooden darning egg, thread and needle
- Color grade overlay: `#D4A043` at 0.04, warm amber tone
- Subtle vignette: radial gradient, edges darkened to `#0A0500` at 0.20

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Hard cut from black. Split line appears instantly. Both panels reveal simultaneously — no fade, immediate presence.
2. **Frame 10-90 (0.33-3s):** Both subjects work. LEFT: developer navigates code, cursor moves, inline suggestion appears. RIGHT: grandmother pulls thread through sock, needle catching lamplight.
3. **Frame 90-150 (3-5s):** Both complete their task simultaneously. LEFT: diff merges, green highlight, code settles. RIGHT: final stitch, thread snipped, sock lowered.
4. **Frame 150-210 (5-7s):** Both hold — a moment of quiet satisfaction on both sides. The parallel is clear.
5. **Frame 210-240 (7-8s):** Hold. Year labels pulse gently once. The split stays clean.

### Typography
- Year labels: Inter, 11px, semi-bold (600), respective colors at 0.25, letter-spacing 3px
- No other text — the visuals carry the narration

### Easing
- Split line reveal: instant (hard cut)
- Year label pulse: `easeInOut(sine)` on 30-frame cycle, opacity 0.25 → 0.35 → 0.25

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

Segment: `cold_open_001`

- **0:00** ("If you use Cursor"): Split appears, both subjects working
- **0:04** ("you're getting really good"): Both complete their tasks simultaneously
- **0:06** ("at this"): Hold on the satisfied parallel

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      <VeoClip clipId="developer_cursor_edit"
        src="/clips/developer_cursor_edit.mp4" fit="cover" />
      <ColorGrade color="#4A90D9" opacity={0.02} />
      <Vignette edgeColor="#000510" edgeOpacity={0.20} />
      <PanelHeader text="2025" color="#4A90D9"
        opacity={0.25} letterSpacing={3} y={36} />
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.12} />

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      <VeoClip clipId="grandmother_darning_hook"
        src="/clips/grandmother_darning_hook.mp4" fit="cover" />
      <ColorGrade color="#D4A043" opacity={0.04} />
      <Vignette edgeColor="#0A0500" edgeOpacity={0.20} />
      <PanelHeader text="1955" color="#D9944A"
        opacity={0.25} letterSpacing={3} y={36} />
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
    "label": "2025",
    "content": "developer_cursor_edit_veo",
    "colorGrade": { "color": "#4A90D9", "opacity": 0.02 },
    "background": "#000000"
  },
  "rightPanel": {
    "label": "1955",
    "content": "grandmother_darning_hook_veo",
    "colorGrade": { "color": "#D4A043", "opacity": 0.04 },
    "background": "#000000"
  },
  "embeddedVeoClips": ["developer_cursor_edit", "grandmother_darning_hook"],
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_001"]
}
```

---
