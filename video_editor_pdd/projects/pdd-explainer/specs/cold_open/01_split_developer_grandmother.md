[split:]

# Section 0.1: Split Screen — Developer with Cursor / Grandmother Darning

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 0:00 - 0:14

## Visual Description

A split-screen composition that opens the entire video. This is the cold open — no title, no preamble. We drop the viewer straight into a visual parallel.

**LEFT PANEL:** A developer at a keyboard, Cursor interface visible on a large monitor, making a slick AI-assisted edit. Cool blue-white monitor glow. Modern workspace. The developer is skilled, efficient — this is what cutting-edge AI-assisted coding looks like.

**RIGHT PANEL:** A 1950s-era grandmother carefully darning a wool sock by lamplight. Warm amber lighting. Practiced hands with a darning needle. Beautiful, expert craftsmanship.

Both complete their tasks simultaneously (beat 2). The code edit lands cleanly; the sock patch finishes neatly. Then the camera zooms out on BOTH sides (beat 3): the developer's single edit is revealed as one of thousands of patches in a massive codebase — files everywhere, diff markers, TODO comments. The grandmother's drawer opens — dozens of carefully mended socks, shirts, trousers. Beat 4 holds the split showing the accumulated weight on both sides.

The split persists across four narration segments covering "If you use Cursor..." through "But here's what your great-grandmother could have told you..."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 60% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clips `developer_cursor_edit_co` → `developer_codebase_zoomout_co` — cool blue-white workspace lighting
- Right panel: clips `grandmother_darning_co` → `grandmother_drawer_zoomout_co` — warm amber lamplight

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen fades in from black. Divider draws downward.
2. **Frame 15-120 (0.5-4s):** Both panels play. LEFT: Developer typing, Cursor autocomplete accepting. RIGHT: Grandmother darning with practiced strokes. Both are skilled.
3. **Frame 120-180 (4-6s):** Both complete their tasks. LEFT: Code edit lands, green checkmark flashes. RIGHT: Sock patch finishes, needle is set down.
4. **Frame 180-300 (6-10s):** Zoom-out on BOTH sides. LEFT: Single edit revealed among massive codebase — file tree expands, diff markers, TODO comments visible. RIGHT: Drawer opens — dozens of mended garments.
5. **Frame 300-420 (10-14s):** Hold. Both sides show accumulated weight. The parallel is unmistakable.

### Typography
- None within panels — narration carries all meaning.

### Easing
- Divider draw: `easeOut(quad)` over 15 frames
- Panel fade-in: `easeOut(quad)` over 15 frames
- Zoom-out: `easeInOut(cubic)` over 90 frames

## Narration Sync
> "If you use Cursor, or Copilot, or Claude Code — you're getting really good at fixing things."
> "But here's what your great-grandmother could have told you about that."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0.00s** (seg 001): Split screen establishes — "If you use Cursor"
- **3.80s** (seg 001 ends): Both panels visible, tasks in progress
- **4.62s** (seg 002): "you're getting really good at" — tasks completing
- **8.92s** (seg 002 ends): Zoom-out begins
- **9.42s** (seg 003): "But here's what your great-grandmother" — accumulated weight visible
- **13.46s** (seg 003 ends): Split holds, weight visible on both sides

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.6}>
    {/* Left panel: developer */}
    <PanelLeft>
      <Sequence from={0} durationInFrames={180}>
        <VeoClip clipId="developer_cursor_edit_co" />
      </Sequence>
      <Sequence from={180}>
        <VeoClip clipId="developer_codebase_zoomout_co" />
      </Sequence>
    </PanelLeft>

    {/* Right panel: grandmother */}
    <PanelRight>
      <Sequence from={0} durationInFrames={180}>
        <VeoClip clipId="grandmother_darning_co" />
      </Sequence>
      <Sequence from={180}>
        <VeoClip clipId="grandmother_drawer_zoomout_co" />
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
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.6 },
  "panels": {
    "left": {
      "clips": ["developer_cursor_edit_co", "developer_codebase_zoomout_co"],
      "label": "Developer with Cursor"
    },
    "right": {
      "clips": ["grandmother_darning_co", "grandmother_drawer_zoomout_co"],
      "label": "Grandmother darning"
    }
  },
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"],
  "durationSeconds": 14.0
}
```

---
