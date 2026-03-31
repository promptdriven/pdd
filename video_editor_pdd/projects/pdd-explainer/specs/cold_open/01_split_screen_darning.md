[split:]

# Section 0.1: Split Screen — Developer Patching vs. Grandmother Darning

**Tool:** Split
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 0:00 - 0:13

## Visual Description

A persistent split-screen composition spanning the first three narration segments. The visual thesis of the entire video: code patching is the modern equivalent of sock darning.

**LEFT PANEL:** A developer at a keyboard with a Cursor-style AI code editor visible on screen. They make a slick AI-assisted edit — a code suggestion appears, they accept it, the diff lands cleanly. Then the camera zooms out to reveal the single edit was one of thousands of patches in a massive codebase: files everywhere, diff markers, TODO comments, tech debt stretching in all directions.

**RIGHT PANEL:** A 1950s great-grandmother carefully darning a wool sock by warm lamplight. Her needle works methodically, closing a hole with neat cross-hatched stitches. Then the camera zooms out to reveal her open drawer — dozens of carefully mended socks, shirts, and trousers, all meticulously repaired. The accumulated weight of careful repair work.

The split holds through three beats: the initial parallel work, the simultaneous task completion, and the dual zoom-out reveal. Both panels progress in lockstep to drive the analogy home.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 30% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clip `developer_cursor_edit` (full duration)
- Right panel: clip `grandmother_darning` (full duration)
- Both panels dim slightly during zoom-out to add gravity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Split screen fades in from black. Divider draws from center outward. Both panels begin.
2. **Frame 15-120 (0.5-4s):** LEFT: Developer typing, Cursor interface visible, AI suggestion appears. RIGHT: Grandmother darning, needle moving through wool. Parallel work established.
3. **Frame 120-180 (4-6s):** Both complete their task simultaneously. LEFT: Code edit lands cleanly, green diff highlight. RIGHT: Sock patch finishes, needle pulls through final stitch.
4. **Frame 180-300 (6-10s):** Dual zoom-out begins. LEFT: Camera pulls back — the single edit is revealed as one patch among thousands. Files, diff markers, TODO comments fill the screen. RIGHT: Grandmother's drawer opens — dozens of mended garments visible.
5. **Frame 300-390 (10-13s):** Hold on the wide view. Both sides show the accumulated weight of careful repair work. A subtle vignette darkens the edges of both panels.
6. **Frame 390-420 (13-14s):** Split screen fades to black, divider dissolves.

### Typography
- None within panels — the visual parallel carries the argument.

### Easing
- Divider draw: `easeOut(cubic)` over 15 frames
- Zoom-out: `easeInOut(cubic)` over 120 frames
- Vignette: `easeIn(quad)` over 60 frames
- Fade-out: `easeIn(quad)` over 30 frames

## Narration Sync
> "If you use Cursor, or Copilot, or Claude Code... you're getting really good at patching."
> "But here's what your great-grandmother could tell you about that."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0.00s** (seg 001): Split screen establishes — developer coding, grandmother darning
- **3.80s** (seg 001 ends): Both working in parallel
- **4.62s** (seg 002): "you're getting really good at patching" — both tasks complete
- **8.92s** (seg 002 ends): Completion beat
- **9.42s** (seg 003): "But here's what your great-grandmother could tell you" — zoom-out begins
- **13.46s** (seg 003 ends): Wide view holds, accumulated weight visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.3}>
    {/* Left panel: developer */}
    <PanelLeft>
      <VeoClip clipId="developer_cursor_edit" />
      <Sequence from={180} durationInFrames={210}>
        <ZoomOut
          from={1.0} to={0.35}
          durationFrames={120} easing="easeInOutCubic"
        />
      </Sequence>
    </PanelLeft>

    {/* Right panel: grandmother */}
    <PanelRight>
      <VeoClip clipId="grandmother_darning" />
      <Sequence from={180} durationInFrames={210}>
        <ZoomOut
          from={1.0} to={0.35}
          durationFrames={120} easing="easeInOutCubic"
        />
      </Sequence>
    </PanelRight>
  </SplitScreen>

  {/* Vignette overlay during zoom-out */}
  <Sequence from={240} durationInFrames={180}>
    <Vignette intensity={0.4} easing="easeInQuad" />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "divider": { "color": "#FFFFFF", "width": 2, "opacity": 0.3 },
  "panels": {
    "left": {
      "clips": ["developer_cursor_edit"],
      "label": "Developer — AI-assisted code patching",
      "zoomOut": { "startFrame": 180, "from": 1.0, "to": 0.35 }
    },
    "right": {
      "clips": ["grandmother_darning"],
      "label": "Grandmother — careful sock darning",
      "zoomOut": { "startFrame": 180, "from": 1.0, "to": 0.35 }
    }
  },
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"],
  "durationSeconds": 14.0
}
```

---
