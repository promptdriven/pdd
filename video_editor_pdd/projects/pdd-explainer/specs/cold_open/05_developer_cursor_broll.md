[veo:]

# Section 0.5: Developer Cursor B-Roll — AI-Assisted Code Edit

**Tool:** Veo (cinematic B-roll)
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:00 - 0:08 (embedded in split screen, full clip length ~10s)

## Visual Description

Over-the-shoulder cinematic footage of a developer working at a modern desk setup. A widescreen monitor displays what is clearly a code editor (dark theme, syntax highlighting visible). The developer's hands rest on a mechanical keyboard; they type a few keystrokes, and a ghosted AI suggestion appears inline in the editor (lighter text, slightly translucent). The developer pauses for a beat, then presses Tab to accept. The suggestion solidifies into real code and a green diff marker appears in the gutter. The developer leans back slightly — task done. The environment is modern tech: standing desk, second monitor, a coffee mug, warm desk lamp providing accent light against the cool glow of the screens.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Aspect ratio: 16:9 native
- Color temperature: Mixed — 6500K from monitors, 3500K from desk lamp

### Chart/Visual Elements
- **Subject:** Developer's hands, keyboard, monitor with code editor
- **Lighting:** Monitor glow as key light (cool blue), desk lamp as accent (warm), ambient room dark
- **Depth of field:** Shallow — f/2.0 equivalent, focus on hands/keyboard with screen slightly soft
- **Camera:** Over-the-shoulder, static with micro-drift (< 1px/s), slight rack to monitor on accept
- **Palette:** Cool blues `#1E293B`, warm amber accent `#D4A043`, green diff `#3FB950`
- **Screen content:** Dark IDE theme, syntax-highlighted code (visible but not readable at this distance)

### Animation Sequence
1. **Frame 0-60 (0-2s):** Camera already in position. Developer types several keystrokes — mechanical keyboard clicks audible.
2. **Frame 60-120 (2-4s):** AI suggestion ghosts in on screen (lighter text). Developer's hands pause, reading.
3. **Frame 120-150 (4-5s):** Developer presses Tab. Suggestion solidifies. Green diff marker appears in gutter.
4. **Frame 150-240 (5-8s):** Developer leans back slightly. Satisfied beat. The warm desk lamp catches the edge of their hand.
5. **Frame 240-300 (8-10s):** Hold on the completed edit. Screen glow illuminates the developer's silhouette.

### Typography
- None — pure cinematic footage

### Easing
- Focus rack: `easeOut(quad)` — natural lens shift
- Camera micro-drift: `linear` — imperceptible

### Veo Prompt
```
Over-the-shoulder cinematic shot of a developer working at a modern desk with a widescreen monitor showing a dark-themed code editor with syntax highlighting. The developer types on a mechanical keyboard, an AI code suggestion appears inline as ghosted lighter text, they press Tab to accept it, and a green diff marker appears in the editor gutter. Modern tech workspace with standing desk, second monitor, coffee mug, and a warm desk lamp providing accent light against the cool blue monitor glow. Shallow depth of field focused on hands and keyboard. Static camera with very slight movement. Professional, focused mood. 16:9, cinematic.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

(This clip plays in the LEFT panel of the split screen during cold_open_001 and cold_open_002.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <VeoClip
    clipId="developer_cursor_edit"
    src="/assets/veo/developer_cursor_edit.mp4"
    startFrom={0}
    playbackRate={1}
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_cursor_edit",
  "duration": 10,
  "frames": 300,
  "camera": "over_the_shoulder_static",
  "colorTemperature": "mixed_6500K_3500K",
  "era": "modern",
  "setting": "modern_tech_workspace",
  "props": ["mechanical_keyboard", "widescreen_monitor", "code_editor", "desk_lamp", "coffee_mug"],
  "keyAction": "accept_ai_suggestion",
  "narrationSegments": ["cold_open_001", "cold_open_002"]
}
```
