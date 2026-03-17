[veo:]

# Section 0.4: Sock Toss — The Economics Punch

**Tool:** Veo
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:15 - 0:20

## Visual Description

Hard cut to modern day. A person standing in a clean, bright modern apartment notices a hole in their sock. They hold it up briefly — deadpan, matter-of-fact — then shrug and toss it in a casual arc toward a small trash bin. The sock lands with a soft bounce. Without hesitation, they reach to a shelf and grab a fresh pair from a cellophane-wrapped multi-pack.

The shot is deliberately casual and modern — daylight streaming through a window, clean minimalist interior. The contrast with the grandmother's careful craft is the entire point. This isn't wasteful; it's rational. The economics shifted.

The camera is locked off on a medium shot, no movement. The action is quick, practical, unstylized. A brief glimpse of a price sticker on the multi-pack: "$4.99."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Modern apartment interior, natural daylight
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium shot, waist-up, slight low angle
- Movement: Static (locked-off tripod)
- Depth of field: moderate, f/4.0 equivalent
- Color grade: clean, neutral, modern — slight desaturation

**Lighting**
- Key light: natural daylight from window, camera-right
- Fill: ambient room light, soft and even
- Overall tone: bright, airy, contemporary — strong contrast with 03's warm amber

**Subject**
- Modern person, casual clothing (t-shirt, jeans)
- Holey sock: visible hole in heel/toe area
- Trash bin: small, simple, white or grey
- Multi-pack: cellophane-wrapped 6-pack of socks, price visible "$4.99"

**Action Beats**
1. Hold up sock, notice hole
2. Shrug (8° shoulder rotation, deadpan expression)
3. Toss in gentle arc toward bin
4. Reach for multi-pack on shelf
5. Hold new pair, turn away

### Animation Sequence

1. **Frame 0-5 (0-0.17s):** Hard cut in (no fade). Person already holding sock, looking at it.
2. **Frame 5-30 (0.17-1.0s):** Person notices hole. Brief inspection. Shrug.
3. **Frame 30-60 (1.0-2.0s):** Sock tossed toward bin. Natural arc. Lands softly.
4. **Frame 60-100 (2.0-3.33s):** Person turns to shelf, grabs multi-pack. Cellophane catches daylight briefly.
5. **Frame 100-130 (3.33-4.33s):** Holds new pair. Price sticker "$4.99" visible. Matter-of-fact expression.
6. **Frame 130-150 (4.33-5.0s):** Hold on the moment. Person starts to turn away. Cut.

### Typography

- None in the footage (price sticker is diegetic — part of the scene)

### Easing

- N/A (live-action, no programmatic easing)

### Veo Prompt

```
Medium shot of a person in a modern apartment holding up a sock with a visible hole. They shrug casually, then toss the sock in a gentle arc into a small trash bin. They turn to a shelf and grab a fresh cellophane-wrapped multi-pack of socks. Natural daylight from a window, clean minimalist interior. The action is quick, practical, unstylized. Slight low angle, static camera, moderate depth of field. Contemporary, everyday, matter-of-fact. Cinematic quality, 24fps.
```

## Narration Sync

> "When socks got cheap enough... she stopped."
Segment: `cold_open_004`
Timing: 0:15 - 0:20

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={150}>
  <VeoClip
    clipId="sock_toss_modern"
    src="/clips/sock_toss_modern.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "sock_toss_modern",
  "camera": {
    "framing": "medium_shot",
    "angle": "slight_low",
    "movement": "static",
    "dof": "moderate"
  },
  "lighting": {
    "key": { "type": "natural_daylight", "position": "camera_right" },
    "fill": "ambient_room",
    "grade": "neutral_contemporary"
  },
  "props": {
    "holeySock": "visible hole in heel area",
    "trashBin": "small white bin",
    "multiPack": { "type": "6-pack socks", "priceSticker": "$4.99" }
  },
  "narrationSegments": ["cold_open_004"],
  "narrationTimingSeconds": { "start": 15.0, "end": 20.0 }
}
```

---
