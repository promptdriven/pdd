[split:]

# Section 0.1: Split Screen Hook — Developer vs Grandmother

**Tool:** Split
**Duration:** ~11s (338 frames @ 30fps)
**Timestamp:** 0:00 - 0:11

## Visual Description

A vertical split screen that anchors the entire video's central metaphor. The screen divides exactly in half — LEFT shows a modern developer making a slick AI-assisted edit in Cursor, RIGHT shows a 1950s great-grandmother carefully darning a wool sock by lamplight. Both are skilled. Both are focused. Both are doing the same thing: patching.

The split holds across four narrative beats:

1. **Beats 1-2 (0:00-5:50):** Both work side by side. The developer types, an AI suggestion appears, they accept it — a clean, efficient edit. The grandmother threads her needle through wool with practiced precision. Both complete their task simultaneously.

2. **Beat 3 (5:82-11:28):** Zoom out on BOTH sides. LEFT reveals the single edit was one of thousands — files everywhere, diff markers, TODO comments, a massive codebase sprawling across tabs and panels. RIGHT reveals the grandmother opening a drawer full of dozens of carefully mended garments — socks, shirts, trousers, all bearing neat patches.

3. **Beat 4 (continues to 11:28):** The split holds. Both sides display the accumulated weight of careful repair work. The visual rhyme is complete: patching is patching, whether it's code or cloth.

The LEFT panel uses the cool blue `#4A90D9` tint of monitor glow. The RIGHT panel uses warm amber `#D9944A` lamplight. The dividing line itself is neutral — the contrast does the storytelling.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#000000` (true black behind panels)
- Split line: 2px vertical divider at x: 960, color `#334155` at 0.15

### Chart/Visual Elements

#### Panel Headers
- LEFT: none initially (pure cinema), then "AI-Assisted Edit" — Inter, 12px, semi-bold (600), `#4A90D9` at 0.0→0.4, letter-spacing 2px, top-left at (40, 30)
- RIGHT: none initially (pure cinema), then "Darning by Lamplight" — Inter, 12px, semi-bold (600), `#D9944A` at 0.0→0.4, letter-spacing 2px, top-right at (920, 30) right-aligned

#### Left Panel — Developer at Keyboard
- Full-bleed Veo clip: `developer_ai_edit` (see companion spec 02)
- Color grade overlay: cool blue `#4A90D9` at 0.04
- Subtle vignette: `#000510` at 0.2 edges

#### Right Panel — Grandmother Darning
- Full-bleed Veo clip: `grandmother_darning` (see companion spec 03)
- Color grade overlay: warm amber `#D9944A` at 0.04
- Subtle vignette: `#1A0E00` at 0.2 edges

#### Zoom-Out Phase (Beat 3, from ~5.82s)
- LEFT: Veo clip transitions to Remotion-rendered zoom-out (see spec 04) showing accumulated codebase
- RIGHT: Veo clip zooms out cinematically to reveal drawer of mended garments (camera pull-back within the Veo clip)

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Hard cut in. Split line appears instantly. Both Veo clips begin simultaneously.
2. **Frame 10-82 (0.33-2.72s):** Both panels play — developer making AI edit, grandmother threading needle. Narration: "If you use Cursor or Copilot or Claude Code..."
3. **Frame 82-165 (2.72-5.50s):** Both complete their tasks simultaneously. Developer's edit lands cleanly. Grandmother's patch finishes neatly. Narration: "...you're getting really good at darning socks."
4. **Frame 165-175 (5.50-5.82s):** Brief hold. Both sides show completed work.
5. **Frame 175-338 (5.82-11.28s):** Zoom-out on both sides. LEFT reveals massive codebase. RIGHT reveals drawer of mended garments. Narration: "Ah, but here's what your grandmother could have told you..."

### Typography
- Panel headers (when visible): Inter, 12px, semi-bold (600), respective panel colors at 0.4, letter-spacing 2px
- No other text overlays — the footage speaks

### Easing
- Split line appear: instant (hard cut)
- Panel header fade: `easeOut(quad)` over 20 frames (starting at frame 90)
- Zoom-out transition: `easeInOut(cubic)` over 30 frames

## Narration Sync
> "If you use Cursor or Copilot or Claude Code, you're getting really good at darning socks."
> "Ah, but here's what your grandmother could have told you: the goal was never to get better at darning."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0:00** ("If you use Cursor"): Split screen appears, both panels active
- **0:03** ("you're getting really good"): Both working, skill visible
- **0:05** ("darning socks"): Both complete their task — the metaphor lands
- **0:06** ("Ah, but here's what"): Zoom-out begins on both sides
- **0:09** ("the goal was never"): Full accumulated weight visible on both sides

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={338}>
  <AbsoluteFill style={{ backgroundColor: '#000000' }}>
    {/* Left panel — Developer */}
    <Panel x={0} width={958}>
      <VeoClip
        clipId="developer_ai_edit"
        src="/clips/developer_ai_edit.mp4"
        fit="cover"
      />
      <ColorGrade color="#4A90D9" opacity={0.04} />
      <Vignette edgeColor="#000510" edgeOpacity={0.2} />

      {/* Zoom-out to accumulated codebase (from frame 175) */}
      <Sequence from={175}>
        <ZoomOutReveal
          fromScale={1.0} toScale={0.15}
          duration={90} easing="easeInOutCubic"
        >
          <AccumulatedCodebase files={42} diffMarkers todoComments />
        </ZoomOutReveal>
      </Sequence>
    </Panel>

    {/* Split divider */}
    <SplitLine x={960} color="#334155" opacity={0.15} width={2} />

    {/* Right panel — Grandmother */}
    <Panel x={962} width={958}>
      <VeoClip
        clipId="grandmother_darning"
        src="/clips/grandmother_darning.mp4"
        fit="cover"
      />
      <ColorGrade color="#D9944A" opacity={0.04} />
      <Vignette edgeColor="#1A0E00" edgeOpacity={0.2} />
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
    "label": "AI-Assisted Edit",
    "labelColor": "#4A90D9",
    "content": "veo_clip",
    "clipId": "developer_ai_edit",
    "colorGrade": { "color": "#4A90D9", "opacity": 0.04 },
    "zoomOutAt": 175,
    "zoomOutContent": "accumulated_codebase"
  },
  "rightPanel": {
    "label": "Darning by Lamplight",
    "labelColor": "#D9944A",
    "content": "veo_clip",
    "clipId": "grandmother_darning",
    "colorGrade": { "color": "#D9944A", "opacity": 0.04 },
    "zoomOutAt": 175,
    "zoomOutContent": "mended_garments_drawer"
  },
  "backgroundColor": "#000000",
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"]
}
```

---
