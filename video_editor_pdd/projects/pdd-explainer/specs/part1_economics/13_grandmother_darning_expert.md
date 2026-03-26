[veo:]

# Section 1.13: Grandmother Darning Expert — Companion Veo Clip

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 7:21 - 7:29

## Visual Description

Close-up of an elderly woman darning a wool sock under warm lamplight. Her hands are experienced, steady — this is a craft she has practiced for decades. A wooden darning egg sits inside the sock. She works a needle and matching wool thread through the worn fabric with practiced, rhythmic strokes.

The lighting is warm, domestic, golden — a single table lamp casting soft shadows. The background is blurred but suggests a comfortable living room. The mood is respectful, not patronizing — this is a master of her craft doing what she does best.

This clip is used in the right panel of Spec 11 (developer_darning_split) as the visual parallel to the developer patching code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Warm domestic interior
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on hands and sock, face partially visible
- Movement: Near-static, subtle drift toward the stitching detail
- Depth of field: Shallow, f/2.0 — hands and sock sharp, background very soft
- Angle: Slightly above, looking down at the hands

**Lighting**
- Key: Warm table lamp `#FFB347` — golden, soft, single-source
- Fill: Natural ambient from room, very low `#E2E8F0` at 0.05
- Shadows: Soft and warm — not harsh
- The wool and wooden egg should catch the lamplight warmly

**Subject**
- Elderly woman: 70s, experienced hands, calm focused expression
- Wool sock: dark navy or charcoal, visible worn patch being repaired
- Darning egg: smooth wood, visible inside the sock
- Needle: thin, catching lamplight

### Animation Sequence
1. **Frame 0-240 (0-8s):** Continuous shot. Grandmother darning. Needle passes through fabric rhythmically. Warm, steady, practiced.

### Typography
- None (pure B-roll footage)

### Easing
- Camera: natural, near-static with warm micro-drift
- Hard cut in and out

### Veo Prompt

```
Close-up shot of an elderly woman's hands darning a dark wool sock under warm golden lamplight. A smooth wooden darning egg sits inside the sock. She works a needle and matching wool thread through the worn fabric with practiced, rhythmic strokes. Shallow depth of field, the hands and sock are sharp while the background living room is softly blurred. Warm single-source table lamp lighting casts gentle shadows. The mood is respectful, dignified, showing a master of a traditional craft. Near-static camera with subtle micro-drift. 8 seconds, cinematic, 24fps.
```

## Narration Sync
> "But they're still darning needles. Faster needles. AI-powered needles. But needles."

Segment: `part1_economics_033`

- **448.18s**: Grandmother darning clip begins (used in right panel of split)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="grandmother_darning_expert"
    src="/clips/grandmother_darning_expert.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning_expert",
  "camera": {
    "framing": "close_up_hands",
    "movement": "near_static_micro_drift",
    "dof": "shallow",
    "aperture": "f/2.0",
    "angle": "slightly_above"
  },
  "lighting": {
    "key": { "color": "#FFB347", "type": "warm_table_lamp" },
    "fill": { "color": "#E2E8F0", "opacity": 0.05, "type": "ambient" }
  },
  "characters": [
    {
      "id": "grandmother_darner",
      "label": "Grandmother",
      "referencePrompt": "Elderly woman in her 70s, experienced steady hands, calm focused expression, working under warm lamplight in a comfortable living room"
    }
  ],
  "narrationSegments": ["part1_economics_033"]
}
```

---
