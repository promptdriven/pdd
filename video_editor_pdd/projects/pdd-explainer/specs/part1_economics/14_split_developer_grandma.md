[split:]

# Section 1.14: Split Screen — Developer with Cursor / Grandmother with Needle

**Tool:** Split
**Duration:** ~17s (510 frames @ 30fps)
**Timestamp:** 7:48 - 8:05

## Visual Description

A split-screen composition that persists across two narration beats. This is a respectful comparison — not dismissive of the tools, but reframing them in terms of the darning metaphor.

**LEFT PANEL:** A developer working efficiently at a keyboard, Cursor interface visible on screen. The lighting is modern, cool blue — contemporary tech workspace. The developer is focused, skilled, productive. This is the lived experience of AI-assisted coding.

**RIGHT PANEL:** A 1950s-era grandmother carefully darning a wool sock by lamplight. Warm amber lighting. Skilled, practiced hands. Beautiful craftsmanship. Not clumsy — expert.

Both are working efficiently. The split holds through "Tools like Cursor and Claude Code are the best darning needles ever made" and into "But they're still darning needles." The second beat zooms out on the developer's side to reveal the massive tangled codebase.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: Two 940px-wide panels with 40px center divider
- Divider: White (#FFFFFF), 2px solid line, 60% opacity
- Background behind divider: Black (#000000)

### Panel Configuration
- Left panel: clip `developer_cursor_p1` — cool blue-white workspace lighting
- Right panel: clip `grandmother_darning_p1` — warm amber lamplight

### Animation Sequence
1. **Frame 0-30 (0-1s):** Split screen establishes from a fade. Divider draws. Both panels show their scenes.
2. **Frame 30-300 (1-10s):** Both panels play simultaneously. LEFT: Developer typing, Cursor suggestions appearing. RIGHT: Grandmother darning with practiced strokes. Both are skilled.
3. **Frame 300-510 (10-17s):** Hold. The parallel is clear without being stated. Both are master craftspeople with the best tools of their era.

### Typography
- None within panels — narration carries all meaning.

### Easing
- Divider fade-in: `easeOut(quad)` over 15 frames
- Panel fade-in: `easeOut(quad)` over 30 frames

## Narration Sync
> "Tools like Cursor and Claude Code are the best darning needles ever made. I use them. They're fantastic."
> "But they're still darning needles. And the fundamental problem with darning isn't speed — it's accumulation."

Segments: `part1_economics_027`, `part1_economics_028`

- **468.49s** (seg 027): Split screen establishes — "Tools like Cursor and Claude Code"
- **475.26s** (seg 027 ends): Both panels visible
- **475.54s** (seg 028): "But they're still darning needles" — zoom out begins on developer side (handled by next spec or late in this split)
- **484.08s** (seg 028 ends): Split dissolves

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={510}>
  <SplitScreen dividerColor="#FFFFFF" dividerWidth={2} dividerOpacity={0.6}>
    {/* Left panel: developer */}
    <PanelLeft>
      <VeoClip clipId="developer_cursor_p1" />
    </PanelLeft>

    {/* Right panel: grandmother */}
    <PanelRight>
      <VeoClip clipId="grandmother_darning_p1" />
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
      "clips": ["developer_cursor_p1"],
      "label": "Developer with Cursor"
    },
    "right": {
      "clips": ["grandmother_darning_p1"],
      "label": "Grandmother darning"
    }
  },
  "narrationSegments": ["part1_economics_027", "part1_economics_028"],
  "durationSeconds": 17.0
}
```

---
