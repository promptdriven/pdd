[veo:]

# Section 0.5: Sock Toss — Modern Disposability

**Tool:** Veo
**Duration:** ~2.5s (74 frames @ 30fps)
**Timestamp:** 0:11 - 0:14

## Visual Description

Hard cut to modern day. A person in a contemporary apartment notices a hole in their sock, shrugs casually, and tosses it into a trash can. The gesture is effortless, without a second thought — no sentimentality, no repair instinct. They reach over and grab a fresh pair from a cellophane-wrapped multi-pack on the counter.

This is the pivot beat of the cold open. The grandmother's careful repair ethic is contrasted with modern disposability. The shot is bright, clean, slightly over-lit compared to the warm lamplight and cool monitor glow of the split screen — the aesthetic shift signals a different era and a different relationship with objects.

The framing is simple: medium shot, eye-level, clean apartment background. The action is quick — notice, shrug, toss. One continuous motion.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern apartment interior — bright, minimal, clean
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium shot — person from waist up, trash can and sock multi-pack visible
- Movement: Static, no movement
- Depth of field: Medium, f/4.0 — subject and nearby objects sharp
- Angle: Eye level, straight-on

**Lighting**
- Key light: Bright natural daylight from window, `#F0EDE8` warm white
- Fill: Ambient room light, clean and even
- Rim: None — flat, modern lighting
- Overall tone: Bright, clean, slightly cool — contemporary feel

**Subject**
- Modern person: casual clothing, 20s-30s, relaxed posture
- Action: notices hole in sock → shrugs → tosses sock in trash → grabs fresh pair from multi-pack
- Props: worn sock with visible hole, small trash can, cellophane-wrapped sock multi-pack

**Key Moments**
- 0-1s: Person holds up a sock, notices a hole. Brief look, casual shrug.
- 1-2s: Sock tossed into nearby trash can. Easy, zero friction.
- 2-2.5s: Hand grabs a fresh pair from a multi-pack on the counter.

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut from split screen. Jarring brightness shift.
2. **Frame 5-30 (0.17-1s):** Person holds sock, notices hole, shrugs.
3. **Frame 30-55 (1-1.83s):** Sock tossed into trash.
4. **Frame 55-74 (1.83-2.5s):** Fresh pair grabbed from multi-pack. Hold briefly.

### Typography
- None (pure B-roll footage)

### Easing
- Hard cut in: instant — no transition from split screen
- All motion is natural/in-camera

### Veo Prompt

```
Medium shot of a person in a bright modern apartment holding up a worn sock and noticing a hole in it. They give a casual shrug and toss the sock into a small trash can beside them. Bright natural daylight from a window, clean minimal apartment interior. Eye-level camera, static framing, medium depth of field. Contemporary casual clothing. The gesture is effortless and indifferent. Cinematic, 24fps. The mood is modern disposability — no sentimentality, just convenience.
```

## Narration Sync
> "When socks got cheap enough, we stopped darning."

Segment: `cold_open_004`

- **0:11** ("When socks got cheap"): Hard cut — person notices hole, shrugs
- **0:13** ("we stopped darning"): Sock tossed in trash, fresh pair grabbed

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={74}>
  <VeoClip
    clipId="sock_toss"
    src="/clips/sock_toss.mp4"
    fit="cover"
  />
  {/* Slight brightness bump — contrast with dark split screen */}
  <ColorGrade brightness={1.05} />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "sock_toss",
  "camera": {
    "framing": "medium_shot_waist_up",
    "movement": "static",
    "dof": "medium",
    "aperture": "f/4.0",
    "angle": "eye_level"
  },
  "lighting": {
    "key": { "color": "#F0EDE8", "position": "window_left", "type": "natural_daylight" },
    "fill": { "color": "#F0EDE8", "opacity": 0.6, "type": "ambient" },
    "rim": "none",
    "grade": "bright_clean_contemporary"
  },
  "props": ["worn_sock_with_hole", "trash_can", "sock_multi_pack"],
  "narrationSegments": ["cold_open_004"]
}
```

---
