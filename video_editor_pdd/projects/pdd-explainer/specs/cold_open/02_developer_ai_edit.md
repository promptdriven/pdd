[veo:]

# Section 0.2: Developer AI Edit — Companion Clip (Split LEFT)

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

Close-up cinematic footage of a developer making a slick AI-assisted code edit. This clip plays in the LEFT panel of the split screen (spec 01). The developer is skilled and focused — hands on a mechanical keyboard, a modern IDE (dark theme) fills a large monitor. An AI suggestion ghost-text appears inline, the developer accepts it with a keystroke, and the edit lands cleanly. The code compiles, a green checkmark or inline validation flashes. One smooth, satisfying interaction.

The lighting is cool blue from the monitor, with a dark office backdrop. The feel is modern, competent, effortless — this person is good at what they do.

The camera holds a tight medium shot on the developer's hands and the lower portion of the screen, keeping the edit visible and the human element present. No camera movement — static framing, shallow depth of field.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark home office, monitor-lit
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium-close — hands on keyboard + lower half of monitor showing code
- Movement: Static, no movement
- Depth of field: Shallow, f/1.8 — keyboard sharp, background softly blurred
- Angle: Slight downward angle, desk-level POV

**Lighting**
- Key light: Cool blue-white monitor glow `#C8D6E5`
- Fill: Minimal dark ambient `#0D1117` at 0.1
- Rim: Faint backlight edge on hands from secondary screen or desk lamp
- Overall tone: Cool, clean, modern — desaturated slightly

**Subject**
- Developer: mid-30s, hands visible on mechanical keyboard
- Monitor: dark-theme IDE with code, AI suggestion ghost-text visible
- Key action: AI suggestion appears → accepted with single keystroke → edit lands

**Key Moments**
- 0-3s: Hands typing. Code visible on screen. IDE dark theme.
- 3-5s: AI suggestion ghost-text appears inline in the editor.
- 5-7s: Developer presses Tab/Enter. Suggestion accepted. Edit inserts cleanly.
- 7-8s: Brief hold on the completed edit. Cursor blinks at end of new line.

### Animation Sequence
1. **Frame 0-90 (0-3s):** Developer typing, code on screen.
2. **Frame 90-150 (3-5s):** AI ghost-text suggestion appears.
3. **Frame 150-210 (5-7s):** Suggestion accepted. Edit lands.
4. **Frame 210-240 (7-8s):** Hold on completed edit.

### Typography
- None (pure B-roll footage)

### Easing
- Hard cut in: instant
- All motion is natural/in-camera

### Veo Prompt

```
Close-up shot of a software developer's hands on a mechanical keyboard, typing code. A large monitor displays a dark-theme code editor with syntax-highlighted code. The developer types confidently and a line of code appears. Cool blue-white monitor glow illuminates the hands and keyboard. Dark home office background, shallow depth of field. Static camera, slightly downward angle from desk level. Cinematic, 24fps, subtle film grain. The mood is skilled competence and modern efficiency.
```

## Narration Sync
> "If you use Cursor or Copilot or Claude Code, you're getting really good at darning socks."

Segment: `cold_open_001`, `cold_open_002`

- **0:00** ("If you use Cursor"): Developer typing, IDE visible
- **0:03** ("you're getting really good"): AI suggestion appears and is accepted
- **0:05** ("darning socks"): Edit complete, clean result visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="developer_ai_edit"
    src="/clips/developer_ai_edit.mp4"
    fit="cover"
  />
  <ColorGrade color="#4A90D9" opacity={0.04} />
  <Vignette edgeColor="#000510" edgeOpacity={0.2} />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_ai_edit",
  "camera": {
    "framing": "medium_close_hands_and_screen",
    "movement": "static",
    "dof": "shallow",
    "aperture": "f/1.8",
    "angle": "slight_downward_desk_level"
  },
  "lighting": {
    "key": { "color": "#C8D6E5", "position": "front_monitor", "type": "screen_glow" },
    "fill": { "color": "#0D1117", "opacity": 0.1, "type": "ambient" },
    "rim": "faint_backlight_edge",
    "grade": "cool_clean_modern"
  },
  "characters": [
    {
      "id": "developer",
      "label": "Developer",
      "referencePrompt": "Software developer, mid-30s, hands visible on mechanical keyboard, wearing casual professional attire. Lit by cool blue-white monitor glow in a dark home office. Large monitor with dark-theme IDE visible."
    }
  ],
  "narrationSegments": ["cold_open_001", "cold_open_002"],
  "parentSplit": "01_split_screen_hook",
  "panelPosition": "left"
}
```

---
