[split:]

# Section 0.1: Split Screen — Developer vs. Grandmother

**Tool:** Split
**Duration:** ~11s
**Timestamp:** 0:00 - 0:11

## Visual Description
A split-screen composition that persists across the first four visual beats of the cold open. The screen is divided vertically into two equal panels separated by a thin white divider.

**LEFT PANEL:** A modern developer at a desk, Cursor IDE visible on their monitor, making an AI-assisted code edit. The edit lands cleanly, then the camera slowly zooms out to reveal thousands of patched files — diff markers, TODO comments, a sprawling codebase of accumulated fixes.

**RIGHT PANEL:** A 1950s grandmother under warm lamplight, carefully darning a wool sock with needle and thread. She finishes her stitch neatly, then the camera pulls back to reveal an open drawer full of dozens of carefully mended garments — socks, shirts, trousers.

Both panels zoom out in sync (starting ~5.8s), transitioning from "one skilled repair" to "the crushing weight of accumulated repair work." The split holds through beat 4, showing the parallel clearly.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with a 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 80% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clips `developer_cursor_edit` and `developer_codebase_zoomout`
- Right panel: clips `grandmother_darning` and `grandmother_drawer_zoomout`
- Each panel crossfades between its close-up and zoom-out clip at ~5.8s

### Animation Sequence
1. **Frame 0-84 (0.0-2.8s):** Both panels show close-up clips. Developer makes an AI edit; grandmother darns a sock. Static split layout.
2. **Frame 84-174 (2.8-5.8s):** Both complete their tasks simultaneously. The code edit lands; the sock patch finishes. Panels still show close-up clips.
3. **Frame 174-240 (5.8-8.0s):** Both panels crossfade (0.5s ease) to their zoom-out clips. LEFT reveals massive patched codebase. RIGHT reveals drawer of mended garments.
4. **Frame 240-330 (8.0-11.0s):** Split holds. Both panels show accumulated weight of careful repair. Slight slow-zoom continues outward on both sides (scale 1.0 → 0.97 over 3s).

### Typography
- None — visuals carry the scene. Narration is audio-only.

### Easing
- Panel crossfade: `easeInOutCubic` over 15 frames
- Slow zoom-out: `linear`

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this. But here's what your great-grandmother figured out sixty years ago."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={330}>
  {/* Split container */}
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2}>
    {/* Left panel: developer */}
    <PanelLeft>
      <Sequence from={0} durationInFrames={189}>
        <VeoClip clipId="developer_cursor_edit" />
      </Sequence>
      <Sequence from={174} durationInFrames={156}>
        <FadeIn durationInFrames={15}>
          <VeoClip clipId="developer_codebase_zoomout" />
        </FadeIn>
      </Sequence>
    </PanelLeft>
    {/* Right panel: grandmother */}
    <PanelRight>
      <Sequence from={0} durationInFrames={189}>
        <VeoClip clipId="grandmother_darning" />
      </Sequence>
      <Sequence from={174} durationInFrames={156}>
        <FadeIn durationInFrames={15}>
          <VeoClip clipId="grandmother_drawer_zoomout" />
        </FadeIn>
      </Sequence>
    </PanelRight>
  </SplitScreen>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.8 },
  "panels": {
    "left": {
      "clips": ["developer_cursor_edit", "developer_codebase_zoomout"],
      "crossfadeAt": 5.8
    },
    "right": {
      "clips": ["grandmother_darning", "grandmother_drawer_zoomout"],
      "crossfadeAt": 5.8
    }
  },
  "durationSeconds": 11.0
}
```
