[veo:]

# Section 1.16: Grandmother Darning — Expert Craftsmanship by Lamplight

**Tool:** Veo
**Duration:** ~8s
**Timestamp:** 7:48 - 7:56

## Visual Description

A medium close-up of an elderly woman's skilled hands darning a wool sock by warm lamplight. The setting is a 1950s-era domestic interior — a comfortable chair, a side table with a sewing basket, warm wood tones. A table lamp provides the primary illumination, casting warm amber light across the scene.

Her hands move with practiced expertise — this is not clumsy or primitive work. The darning needle weaves through the fabric with fluid, confident strokes. The sock is quality wool, the repair careful and thorough. This is a master craftswoman with the best tool of her era.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Framing: Medium close-up on hands and sock
- Color temperature: Warm amber lamplight

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up of hands darning, sock filling lower-center frame
- Movement: Static with natural gentle sway
- Depth of field: Shallow, f/2.8 — hands and sock sharp, background soft
- Angle: Slightly elevated, looking down at the work

**Lighting**
- Key: Warm amber table lamp `#FFB347` at 0.7, from upper-right
- Fill: Soft warm ambient `#D4A574` at 0.15
- Background: Soft out-of-focus warm tones from domestic interior

**Subject**
- Elderly woman's hands, skilled and steady
- Quality wool sock with visible repair area
- Darning needle and thread visible
- Sewing basket partially visible at edge of frame

### Veo Prompt
```
Close-up of elderly woman's hands expertly darning a wool sock by warm lamplight. 1950s domestic interior setting with a comfortable chair and side table. Table lamp casts warm amber light. Skilled, practiced darning strokes with a needle through quality wool fabric. Sewing basket partially visible. Shallow depth of field with soft warm background. Period-appropriate details. Cinematic 24fps, intimate warm tone. The mood is practiced expertise and quiet dedication.
```

### Animation Sequence
1. **0-4s:** Hands working the darning needle through the sock. Fluid, expert movements.
2. **4-8s:** Continue darning. The needle catches the light as it moves through the fabric.

### Typography
- None (pure B-roll)

### Easing
- N/A (live-action footage)

## Narration Sync
> "Tools like Cursor and Claude Code are the best darning needles ever made."

Segment: `part1_economics_027`

- **468.49s**: Grandmother darning as narration begins (plays simultaneously in split-screen right panel)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="grandmother_darning_p1"
    src="/clips/grandmother_darning_p1.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning_p1",
  "camera": {
    "framing": "medium_close_up",
    "movement": "static_with_sway",
    "dof": "shallow",
    "aperture": "f/2.8",
    "angle": "elevated"
  },
  "lighting": {
    "key": { "color": "#FFB347", "opacity": 0.7, "type": "table_lamp" },
    "fill": { "color": "#D4A574", "opacity": 0.15, "type": "ambient" }
  },
  "characters": [
    {
      "id": "grandmother",
      "label": "Grandmother",
      "referencePrompt": "Elderly woman in 1950s domestic setting, skilled hands darning wool socks by lamplight, warm amber tones"
    }
  ],
  "narrationSegments": ["part1_economics_027"]
}
```

---
