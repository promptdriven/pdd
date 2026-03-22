[veo:]

# Section 0.1a: Developer AI Edit — Companion Clip

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:00 - 0:05

## Visual Description

Companion Veo clip for the LEFT panel of the split screen hook (spec `01_split_screen_hook.md`). This clip will be masked to the left half of frame.

A developer's hands on a modern keyboard, with a large monitor showing a dark-themed code editor (Cursor/VS Code style). An inline AI code suggestion appears — a ghosted autocomplete spanning several lines. The developer's right hand moves to press Tab or Enter, accepting the suggestion. The ghosted code solidifies into real code. The edit is clean, fast, satisfying.

The framing is medium-close: hands on keyboard in the lower third, monitor filling the upper two-thirds. The developer's face is partially visible at the top edge, lit by cool blue monitor glow. The focus is on the hands and screen — the action of the edit.

Color grade: cool blue from monitor light, sharp and modern. Dark office/home office background. Minimal ambient light.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9) — will be cropped to left 958px in split
- Background: Dark office, monitor-lit

### Chart/Visual Elements

**Camera**
- Framing: medium-close on hands + keyboard + monitor
- Movement: static — no pan, no dolly, no rack focus
- Depth of field: moderate, f/2.8 — keyboard and screen both in focus
- Angle: slightly elevated, looking down at desk/keyboard at ~15°

**Lighting**
- Key: cool blue-white monitor glow `#B8D4F0`, direct from screen
- Fill: dim ambient room light, neutral `#1A1A2E` at 0.1
- No rim light — single-source monitor look
- Overall: cool, clean, modern

**Subject**
- Hands: on a modern mechanical or low-profile keyboard
- Screen: dark-themed IDE, visible code, inline AI suggestion appearing as ghosted text
- Action: accept the suggestion with a keystroke, ghosted text solidifies

### Animation Sequence
1. **Frame 0-60 (0-2s):** Hands on keyboard. Screen shows code. An AI suggestion begins to appear as ghosted/dimmed text inline.
2. **Frame 60-120 (2-4s):** Developer reads the suggestion briefly. Hand moves toward Tab/Enter key.
3. **Frame 120-150 (4-5s):** Keystroke. Ghosted code solidifies. The edit lands.
4. **Frame 150-180 (5-6s):** Hold. Clean code on screen. Hands rest.

### Typography
- None (pure B-roll)

### Easing
- Natural video — no programmatic easing

### Veo Prompt

```
Medium-close shot of a software developer's hands on a sleek modern keyboard, large monitor above showing a dark-themed code editor. An inline code suggestion appears as ghosted semi-transparent text in the editor. The developer presses a key to accept the suggestion and the ghosted code becomes solid. Cool blue-white monitor glow lights the hands and keyboard. Dark office background with minimal ambient light. Slightly elevated camera angle looking down at the desk. Static camera, no movement. Cinematic shallow depth of field. Modern, clean, professional atmosphere. 24fps with subtle film grain.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."

Segment: `cold_open_001`

- **0:00**: Hands visible, IDE on screen, AI suggestion appearing
- **2.72s**: Suggestion accepted, code lands

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="developer_ai_edit"
    src="/clips/developer_ai_edit.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_ai_edit",
  "camera": {
    "framing": "medium_close_hands_and_monitor",
    "movement": "static",
    "dof": "moderate",
    "aperture": "f/2.8",
    "angle": "slightly_elevated_15deg"
  },
  "lighting": {
    "key": { "color": "#B8D4F0", "position": "front_monitor", "type": "screen_glow" },
    "fill": { "color": "#1A1A2E", "opacity": 0.1, "type": "ambient" },
    "grade": "cool_modern"
  },
  "characters": [
    {
      "id": "developer",
      "label": "Developer",
      "referencePrompt": "Software developer, mid-30s, casual professional attire. Only hands and partial face visible. Lit by cool blue-white monitor glow in dark office. Modern keyboard and large monitor with dark-themed IDE."
    }
  ],
  "narrationSegments": ["cold_open_001"],
  "narrationTimingSeconds": { "start": 0, "end": 5 }
}
```

---
