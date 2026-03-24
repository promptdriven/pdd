[veo:]

# Section 1.13: Developer Cursor Coding — Companion Veo Clip

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 5:20 - 5:28

## Visual Description

A close-up of a developer's hands on a mechanical keyboard, typing with purpose. A large monitor fills the background, showing a modern code editor (Cursor-like interface) with dark theme. Code suggestions appear in ghost text and are accepted with a quick Tab key press. The developer's hands are confident — this is someone who knows their tools.

The lighting is cool blue-white from the monitor, with ambient office light filling softly from the side. Modern, clean workspace. The feel is professional competence — this clip must not be dismissive.

This clip is embedded within the left panel of 12_developer_darning_split.md.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern office/home office, dark monitor glow dominant
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up (MCU) on hands and keyboard, monitor in background
- Movement: static, locked-off — observational
- Depth of field: shallow, f/2.0 — hands sharp, monitor slightly soft
- No drift or push-in

**Lighting**
- Key light: cool blue-white `#B8D4E8` from monitor, dominant
- Fill: warm ambient `#E8D5B8` at 0.3 from side (desk lamp or window)
- Monitor glow creates rim lighting on fingers
- Overall tone: modern, cool, professional

**Subject**
- Developer's hands on mechanical keyboard
- Monitor showing dark-themed code editor with syntax highlighting
- Clean desk, minimal clutter
- No face visible — hands and workspace only

**Key Moments**
- 0-3s: Hands typing steadily. Code editor visible with colorful syntax.
- 3-6s: A ghost-text suggestion appears on screen. Quick Tab press to accept.
- 6-8s: Continue typing. The flow is natural and productive.

### Animation Sequence
1. **Frame 0-90 (0-3s):** Hands typing on keyboard. Monitor shows code scrolling.
2. **Frame 90-180 (3-6s):** Brief pause. Code suggestion appears (visible as lighter ghost text on monitor). Tab press — suggestion accepted.
3. **Frame 180-240 (6-8s):** Resume typing. Productive flow continues.

### Typography
- None (pure B-roll footage)

### Easing
- Fade-in: `easeOut(quad)`, 0.5s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Close-up of a developer's hands typing on a mechanical keyboard in a dimly lit modern office. A large monitor displays a dark-themed code editor with colorful syntax highlighting. The developer types steadily and purposefully. Cool blue-white light from the monitor illuminates the hands. Warm ambient fill light from the side. Shallow depth of field, f/2.0, hands sharp, monitor slightly soft. Static locked-off camera. Clean modern workspace, no face visible. Professional and competent feel. Cinematic, 24fps, clean cool color grade.
```

## Narration Sync

> "Tools like Cursor and Claude Code are the best darning needles ever made."

Segment: `part1_economics_032`
Timing: 5:20 - 5:28 (embedded in left panel of 12_developer_darning_split)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="developer_cursor_coding"
    src="/clips/developer_cursor_coding.mp4"
    fit="cover"
  />
  <Sequence from={0} durationInFrames={15}>
    <FadeIn />
  </Sequence>
  <Sequence from={230} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_cursor_coding",
  "camera": {
    "framing": "medium_close_up",
    "movement": "static",
    "dof": "shallow",
    "drift": false
  },
  "lighting": {
    "key": { "color": "#B8D4E8", "position": "monitor", "type": "cool_blue" },
    "fill": { "color": "#E8D5B8", "position": "side", "type": "ambient" },
    "grade": "cool_professional"
  },
  "embeddedIn": "12_developer_darning_split",
  "panel": "left",
  "narrationSegments": ["part1_economics_032"],
  "narrationTimingSeconds": { "start": 441.12, "end": 447.88 }
}
```

---
