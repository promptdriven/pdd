[veo:]

# Section 0.4: Sock Toss — When Socks Got Cheap

**Tool:** Veo
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:11 - 0:14

## Visual Description

Hard cut from the split screen to a completely different world: modern day. A person in a contemporary living space notices a hole in their sock. They shrug casually, toss the sock into a trash can, and grab a fresh pair from a multi-pack on the shelf. The gesture is effortless, almost dismissive — the sock has no value worth saving.

The tone shifts dramatically from the warm nostalgia of the grandmother scene to bright, casual modernity. The lighting is natural daylight. The action is quick and unthinking — this is not a considered decision, it's muscle memory. The contrast with the grandmother's painstaking repair work makes the economic argument visually.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern apartment / bedroom — clean, bright
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium shot — person seated or standing, waist up, laundry area or bedroom
- Movement: Static with slight handheld feel — documentary casual
- Depth of field: Moderate, f/4.0 — subject and environment both readable
- Angle: Eye level, straight on — matter-of-fact framing

**Lighting**
- Key light: Natural daylight from window `#E8E0D4`, soft and diffused
- Fill: Bounced ambient light — bright, airy room
- Rim: None — flat, modern, un-cinematic by design (contrast with the grandmother's dramatic lamplight)
- Overall tone: Bright, casual, slightly overexposed — throwaway feeling

**Subject**
- Person: Young adult, 20s-30s, casual clothes (t-shirt, sweatpants)
- Action: Notices hole in sock → shrugs → tosses sock into trash → grabs fresh pair from a multi-pack
- Expression: Casual indifference — not wasteful, just practical
- Props: Holey sock, small trash can, multi-pack of new socks on a shelf

### Animation Sequence
1. **Frame 0-5 (0-0.17s):** Hard cut from split screen. Bright modern room.
2. **Frame 5-40 (0.17-1.3s):** Person holds sock, notices hole, shrugs.
3. **Frame 40-65 (1.3-2.2s):** Tosses sock into trash can. Casual, fluid motion.
4. **Frame 65-90 (2.2-3s):** Grabs a fresh pair from the multi-pack. Pulls them on or holds them up.

### Typography
- None (pure B-roll footage)

### Easing
- Hard cut in: instant (no fade — jarring contrast is intentional)
- Hard cut out: instant (to code scene)

### Veo Prompt

```
Medium shot of a young adult in casual clothes in a bright modern apartment. They hold up a sock and notice a hole in it. They shrug casually and toss the sock into a small trash can nearby. Natural daylight from a window, bright and airy room. Static camera with slight handheld feel. Moderate depth of field. The mood is casual indifference — the sock is not worth saving. Contemporary, documentary-style, 24fps.
```

## Narration Sync
> "When socks got cheap enough, she stopped."

Segment: `cold_open_004`

- **0:11** ("When socks got cheap enough"): Person notices hole, shrugs, tosses sock
- **0:13** ("she stopped"): Grabs fresh pair — the action is already done, effortless

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <VeoClip
    clipId="sock_toss"
    src="/clips/sock_toss.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "sock_toss",
  "camera": {
    "framing": "medium_shot",
    "movement": "static_handheld",
    "dof": "moderate",
    "aperture": "f/4.0",
    "angle": "eye_level"
  },
  "lighting": {
    "key": { "color": "#E8E0D4", "position": "window", "type": "natural_daylight" },
    "fill": { "color": "#F5F0E8", "opacity": 0.6, "type": "bounced_ambient" },
    "rim": "none",
    "grade": "bright_casual_modern"
  },
  "props": ["holey_sock", "trash_can", "sock_multipack"],
  "narrationSegments": ["cold_open_004"],
  "narrationTimingSeconds": { "start": 11.46, "end": 13.94 }
}
```

---
