[veo:]

# Section 1.12: Developer Cursor Coding — Companion Veo Clip

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 7:21 - 7:29

## Visual Description

Close-up of a software developer working at a modern desk setup. A dark-themed code editor (Cursor/VS Code style) fills their monitor. The developer is focused and productive — typing, occasionally pausing to review, making edits. The mood is competent, professional, efficient.

The monitor glow is the primary light source, casting a cool blue-white on the developer's face. A second monitor or ambient desk lamp provides soft warm fill. The desk is clean and modern — not cluttered.

This clip is used in the left panel of Spec 11 (developer_darning_split) and embodies the "these tools ARE impressive" side of the argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern home office or studio
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up, over-the-shoulder angle showing both the developer and their screen
- Movement: Very subtle drift, almost static — the developer and their work are the subject
- Depth of field: Shallow, f/2.8 — developer and screen sharp, background soft
- Angle: Slightly elevated, looking down at a ~15° angle

**Lighting**
- Key: Monitor glow `#E2E8F0` — cool, technical
- Fill: Warm ambient `#FFB347` at 0.15 from desk lamp or second monitor
- Background: Dark, minimal, uncluttered
- No visible windows or distracting elements

**Subject**
- Developer: Mid-30s, focused expression, typing on a modern keyboard
- Screen: Dark-themed code editor with syntax highlighting visible (but not readable)
- Hands visible on keyboard, actively coding

### Animation Sequence
1. **Frame 0-240 (0-8s):** Continuous shot. Developer coding. Occasional pause to review code on screen. Subtle hand movements. Monitor glow shifts slightly as they scroll through code.

### Typography
- None (pure B-roll footage)

### Easing
- Camera: natural, near-static with micro-movement
- Hard cut in and out

### Veo Prompt

```
Medium close-up over-the-shoulder shot of a software developer working at a clean modern desk. Dark-themed code editor with syntax highlighting fills the monitor screen. The developer is focused, typing on a mechanical keyboard, occasionally pausing to review code. Cool blue-white monitor glow is the primary light source on their face, with soft warm ambient fill from a desk lamp. Shallow depth of field, background softly blurred. The mood is competent, productive, professional. Near-static camera with subtle micro-drift. 8 seconds, cinematic, 24fps.
```

## Narration Sync
> "But they're still darning needles. Faster needles. AI-powered needles. But needles."

Segment: `part1_economics_033`

- **448.18s**: Developer coding clip begins (used in left panel of split)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="developer_cursor_coding"
    src="/clips/developer_cursor_coding.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "developer_cursor_coding",
  "camera": {
    "framing": "medium_close_up_ots",
    "movement": "near_static_micro_drift",
    "dof": "shallow",
    "aperture": "f/2.8",
    "angle": "slightly_elevated"
  },
  "lighting": {
    "key": { "color": "#E2E8F0", "type": "monitor_glow" },
    "fill": { "color": "#FFB347", "opacity": 0.15, "type": "ambient_desk_lamp" }
  },
  "characters": [
    {
      "id": "developer_protagonist",
      "label": "Developer",
      "referencePrompt": "Mid-30s software developer, focused expression, modern casual attire, working at a clean desk with dark-themed code editor"
    }
  ],
  "narrationSegments": ["part1_economics_033"]
}
```

---
