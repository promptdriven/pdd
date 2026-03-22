[veo:]

# Section 0.3: Sock Toss — She Stopped

**Tool:** Veo
**Duration:** ~3s (90 frames @ 30fps)
**Timestamp:** 0:11 - 0:14

## Visual Description

Hard cut to modern day. A person discovers a hole in their sock, shrugs casually, and tosses it into a wastebasket. The gesture is effortless and unbothered — the opposite of the grandmother's careful, time-intensive repair. This is the punchline of the setup.

The shot is clean and bright — modern apartment or laundry room. Natural daylight. The person holds up a sock with a visible hole, glances at it for a beat, then drops it into a small trash can with a dismissive toss. No drama, no ceremony. The sock is disposable now.

The color grade is neutral and bright — modern, casual, everyday. A strong contrast to the warm amber nostalgia of the grandmother and the cool blue intensity of the developer.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Bright modern interior, daylight

### Chart/Visual Elements

**Camera**
- Framing: medium shot — person from waist up, wastebasket visible at lower frame edge
- Movement: static — no camera movement
- Depth of field: moderate, f/3.5 — subject and nearby environment in focus
- Angle: eye level, straight on

**Lighting**
- Key: natural daylight from window, soft and bright `#F5F0E8`
- Fill: ambient room light, neutral warm `#E8E0D4`
- No dramatic lighting — flat, everyday, casual
- Overall: bright, neutral, modern

**Subject**
- Person: casual, any age 25-45, wearing comfortable clothes
- Action: holds up a sock with visible hole, brief glance, then tosses it into wastebasket
- Expression: slight shrug, unbothered — this is not a decision that requires thought
- Props: sock with hole, small wastebasket or trash can

### Animation Sequence
1. **Frame 0-30 (0-1s):** Person holds up a sock, examines the hole briefly.
2. **Frame 30-60 (1-2s):** Slight shrug. Casual toss toward wastebasket.
3. **Frame 60-90 (2-3s):** Sock lands in basket. Person turns away or reaches for a fresh pair.

### Typography
- None (pure B-roll)

### Easing
- Hard cut in: instant (from previous zoom-out)
- Natural video playback
- Hard cut out: to code regeneration spec

### Veo Prompt

```
Medium shot of a person in a bright modern apartment holding up a sock with a visible hole. Natural daylight from a window illuminates the scene. The person glances at the hole, gives a slight casual shrug, and tosses the sock into a small wastebasket beside them. The gesture is effortless and unbothered. Bright neutral color grade, everyday modern interior. Static camera at eye level. Moderate depth of field. The mood is casual indifference — disposing of something that is no longer worth repairing. 24fps, clean natural lighting, no dramatic shadows.
```

## Narration Sync
> "When socks got cheap enough, she stopped."

Segment: `cold_open_004`

- **11.46s** ("When socks got cheap enough"): Person holds up holed sock, shrugs
- **13.50s** ("she stopped"): Sock tossed into wastebasket — punchline lands

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
    "movement": "static",
    "dof": "moderate",
    "aperture": "f/3.5",
    "angle": "eye_level"
  },
  "lighting": {
    "key": { "color": "#F5F0E8", "position": "window", "type": "natural_daylight" },
    "fill": { "color": "#E8E0D4", "type": "ambient" },
    "grade": "bright_neutral_modern"
  },
  "props": ["sock_with_hole", "wastebasket"],
  "narrationSegments": ["cold_open_004"],
  "narrationTimingSeconds": { "start": 11.46, "end": 13.94 }
}
```

---
