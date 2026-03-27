[split:]

# Section 0.1: Split Screen — Developer Darning Code vs. Grandmother Darning Socks

**Tool:** Split
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 0:00 - 0:09

## Visual Description
A split-screen composition that persists across four narration beats, establishing the central metaphor of the cold open: AI-assisted code editing IS darning.

**LEFT PANEL:** A developer at a keyboard with a Cursor-like IDE interface visible, making a slick AI-assisted edit. The edit completes cleanly — a single function patched. Then the camera zooms out to reveal the single edit is one of thousands of patches in a massive codebase. Files everywhere, diff markers, TODO comments. The accumulated weight of careful repair work.

**RIGHT PANEL:** A 1950s great-grandmother carefully darning a wool sock by warm lamplight. She completes a neat patch. Then the camera zooms out to reveal her open drawer — dozens of carefully mended socks, shirts, trousers. The accumulated weight of careful repair work mirrors the code side.

The split holds through four segments: the initial task, the completion, the zoom-out reveal, and the "accumulated weight" beat. Both panels progress in parallel, creating a visual rhyme.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 40% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clip `developer_cursor_edit` (0:00-5:22), then clip `developer_codebase_zoomout` (5:34-8:66)
- Right panel: clip `grandmother_darning` (0:00-5:22), then clip `grandmother_drawer_zoomout` (5:34-8:66)
- Transition between clips: 10-frame crossfade at segment boundary

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen fades in from black. Divider appears. Both panels begin simultaneously.
2. **Frame 15-108 (0.5-3.6s):** LEFT: Developer making an AI-assisted edit in Cursor. Code highlights, inline suggestion appears and is accepted. RIGHT: Grandmother darning a wool sock by lamplight. Needle moves through fabric with practiced precision.
3. **Frame 113-157 (3.76-5.22s):** Both complete their tasks simultaneously. LEFT: The code edit lands cleanly — green diff indicator. RIGHT: The sock patch finishes neatly — thread snipped.
4. **Frame 160-260 (5.34-8.66s):** Zoom out on both sides. LEFT: Camera pulls back to reveal massive codebase — hundreds of files with diff markers, TODO comments, patch annotations. RIGHT: Grandmother's drawer opens — dozens of carefully mended garments. Both sides show the accumulated weight of all that careful repair work.
5. **Frame 260-270 (8.66-9.0s):** Hold. The parallel is unmistakable. Split screen holds for a beat before the hard cut.

### Typography
- None within panels — narration carries the meaning. The visual parallel provides the labeling.

### Easing
- Divider fade-in: `easeOut(quad)` over 15 frames
- Panel crossfade: `easeInOut(cubic)` over 10 frames
- Final hold: static

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."
> "...you're getting really good at this."
> "But here's what your great-grandmother figured out sixty years ago."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0.00s** (seg 001): Split screen establishes — developer editing, grandmother darning
- **3.60s** (seg 001 ends): Both tasks complete simultaneously
- **3.76s** (seg 002): "You're getting really good at this" — completion moment
- **5.34s** (seg 003): Zoom out begins — reveal the accumulated weight
- **8.66s** (seg 003 ends): Split holds, showing parallel accumulation

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.4}>
    {/* Left panel: developer */}
    <PanelLeft>
      <Sequence from={0} durationInFrames={160}>
        <VeoClip clipId="developer_cursor_edit" />
      </Sequence>
      <Sequence from={150} durationInFrames={120}>
        <FadeIn duration={10}>
          <VeoClip clipId="developer_codebase_zoomout" />
        </FadeIn>
      </Sequence>
    </PanelLeft>

    {/* Right panel: grandmother */}
    <PanelRight>
      <Sequence from={0} durationInFrames={160}>
        <VeoClip clipId="grandmother_darning" />
      </Sequence>
      <Sequence from={150} durationInFrames={120}>
        <FadeIn duration={10}>
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
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.4 },
  "panels": {
    "left": {
      "clips": ["developer_cursor_edit", "developer_codebase_zoomout"],
      "label": "Developer patching code"
    },
    "right": {
      "clips": ["grandmother_darning", "grandmother_drawer_zoomout"],
      "label": "Grandmother darning socks"
    }
  },
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"],
  "durationSeconds": 9.0
}
```

---
