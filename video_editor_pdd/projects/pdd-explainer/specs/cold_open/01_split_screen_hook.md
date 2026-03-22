[split:]

# Section 0.1: Split Screen Hook

**Tool:** Split
**Duration:** ~5s
**Timestamp:** 0:00 - 0:05

## Visual Description
Split-screen comparison. LEFT panel: a modern developer at a desk, screen-glow lighting, making a slick AI-assisted code edit — cursor moves, code appears, diff highlights green. RIGHT panel: a 1950s great-grandmother darning a wool sock under warm amber lamplight, needle pulling thread through fabric. Both complete their respective tasks simultaneously — the code lands cleanly on the left as the stitch finishes neatly on the right. A thin vertical divider (1px, #FFFFFF20) separates the two panels.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Layout: 50/50 vertical split (960px each)
- Divider: 1px solid line, color #FFFFFF20
- Background: N/A (each panel is a full-bleed video clip)

### Split Panels
- **Left panel (960x1080):** Veo clip `developer_ai_edit` — modern developer, dark room, screen glow
- **Right panel (960x1080):** Veo clip `grandmother_darning` — 1950s grandmother, amber lamplight, darning sock

### Animation Sequence
1. **Frame 0-10 (0-0.3s):** Both panels fade in simultaneously from black (opacity 0 → 1)
2. **Frame 10-120 (0.3-4.0s):** Both clips play in sync — developer edits code, grandmother stitches sock
3. **Frame 120-150 (4.0-5.0s):** Hold on completed actions — both tasks visually "land" at the same beat

### Typography
- No text overlays in this composition

### Easing
- Panel fade-in: `easeOutCubic`

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <SplitScreen dividerColor="#FFFFFF20">
    <LeftPanel>
      <VeoClip clipId="developer_ai_edit" />
    </LeftPanel>
    <RightPanel>
      <VeoClip clipId="grandmother_darning" />
    </RightPanel>
  </SplitScreen>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "split_screen",
  "layout": "vertical_50_50",
  "leftClipId": "developer_ai_edit",
  "rightClipId": "grandmother_darning",
  "divider": { "width": 1, "color": "#FFFFFF20" }
}
```
