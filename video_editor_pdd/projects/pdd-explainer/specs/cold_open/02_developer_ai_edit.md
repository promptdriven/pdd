[veo:]

# Section 0.2: Developer AI Edit — Cursor in Action

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:00 - 0:06

## Visual Description

A cinematic close-up of a developer making an AI-assisted code edit using Cursor IDE. The developer is focused and skilled — hands moving confidently across a mechanical keyboard. The monitor shows a dark-themed IDE with an inline AI suggestion appearing and being accepted. The edit lands cleanly: a function gets patched, a green diff highlight appears, and the code looks better than before.

The lighting is modern and cool — dominated by the blue-white glow of the monitor in a dim room. The mood is competence and efficiency. This is someone who is *good* at what they do.

This clip is used as the LEFT panel in the `01_split_screen_hook` split composition.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark home office / desk environment
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on hands and keyboard, with monitor visible in background, then medium shot showing face + screen
- Movement: Subtle drift right, settling on monitor content
- Depth of field: Moderate, f/2.8 — keyboard sharp, monitor slightly soft initially
- Angle: Eye-level, slightly angled to show both hands and screen

**Lighting**
- Key light: Cool blue-white monitor glow `#B8C9E0`
- Fill: Faint warm ambient from desk lamp `#3D2F1F` at 0.1
- Rim: Subtle edge light on hands from keyboard backlight `#4A90D9` at 0.15
- Overall tone: Modern, clean, competent

**Subject**
- Developer: Confident, mid-20s to mid-30s, casual attire
- Action: Types briefly, accepts an AI inline suggestion, watches code update
- Expression: Focused satisfaction — the edit was clean
- Screen content: Dark-themed IDE (VS Code / Cursor style), inline AI suggestion ghost text appearing

### Animation Sequence
1. **Frame 0-60 (0-2s):** Close-up on hands typing. Keyboard clicks. Monitor glow illuminates fingers.
2. **Frame 60-120 (2-4s):** Pull slightly wider. AI suggestion appears as ghost text on screen. Developer's hand moves to accept.
3. **Frame 120-180 (4-6s):** The edit lands. Green diff highlight. Clean function. Developer leans back slightly — satisfaction.

### Typography
- None (pure B-roll footage)

### Easing
- Camera drift: natural handheld micro-movement
- Hard cut in and out (used within split composition)

### Veo Prompt

```
Close-up shot of a software developer's hands on a mechanical keyboard, typing code. A large monitor in the background shows a dark-themed code editor with syntax-highlighted code. The developer accepts an inline AI code suggestion — ghost text appears and solidifies into real code. Cool blue-white monitor glow illuminates the hands and keyboard. Dim modern home office environment. Subtle camera drift from hands toward the monitor. Shallow depth of field, cinematic, 24fps. The mood is quiet competence and modern efficiency.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."

Segment: `cold_open_001`

- **0:00** ("If you use Cursor"): Hands on keyboard, typing
- **0:02** ("Claude Code"): AI suggestion appears on screen
- **0:04** ("Copilot"): Edit accepted, code looks clean

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
    "framing": "close_up_hands_to_medium",
    "movement": "subtle_drift_right",
    "dof": "moderate",
    "aperture": "f/2.8",
    "angle": "eye_level"
  },
  "lighting": {
    "key": { "color": "#B8C9E0", "position": "front_monitor", "type": "screen_glow" },
    "fill": { "color": "#3D2F1F", "opacity": 0.1, "type": "desk_lamp" },
    "rim": { "color": "#4A90D9", "opacity": 0.15, "type": "keyboard_backlight" },
    "grade": "cool_modern"
  },
  "characters": [
    {
      "id": "developer",
      "label": "Developer",
      "referencePrompt": "Software developer, mid-20s to mid-30s, casual attire, confident and focused. Hands on mechanical keyboard. Lit by cool blue-white monitor glow in a dim modern home office."
    }
  ],
  "usedIn": "01_split_screen_hook (left panel)",
  "narrationSegments": ["cold_open_001"]
}
```

---
