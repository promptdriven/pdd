[veo:]

# Section 0.1b: Grandmother Darning — Companion Clip

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:00 - 0:05

## Visual Description

Companion Veo clip for the RIGHT panel of the split screen hook (spec `01_split_screen_hook.md`). This clip will be masked to the right half of frame.

An elderly woman's hands carefully darning a wool sock by warm lamplight. Her movements are practiced and deliberate — needle pulling thread through the fabric in a cross-hatch repair pattern over a small hole. The sock is dark wool, the thread a slightly different shade. A wooden darning egg or mushroom is visible inside the sock, providing tension.

The framing matches the developer shot: medium-close on hands in the lower third, the sock and darning work filling frame. Her face is partially visible at the top edge, lit warmly by a table lamp or floor lamp. The setting suggests a 1950s-60s parlor — a comfortable chair, warm textures, soft focus background.

Color grade: warm amber from lamplight, soft and slightly diffused. Nostalgic but not sepia — real warmth, not a filter.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9) — will be cropped to right 958px in split
- Background: Warm-lit parlor/living room, period-appropriate

### Chart/Visual Elements

**Camera**
- Framing: medium-close on hands + sock + darning work
- Movement: static — no movement
- Depth of field: shallow, f/2.0 — hands and sock sharp, background soft
- Angle: slightly elevated, matching developer shot angle (~15°)

**Lighting**
- Key: warm amber lamplight `#F5D6A8`, from table/floor lamp at camera-right
- Fill: warm ambient room light `#3D2B1A` at 0.15
- Subtle rim/edge light on hands from lamp
- Overall: warm, soft, nostalgic — natural incandescent quality

**Subject**
- Elderly woman, 70s-80s — only hands and partial face visible
- Hands: experienced, careful, threading a darning needle through wool sock
- Props: dark wool sock, darning needle, thread, wooden darning egg/mushroom
- Setting hints: comfortable upholstered chair arm, warm textured background
- Action: steady, practiced cross-hatch stitching over a small hole

### Animation Sequence
1. **Frame 0-60 (0-2s):** Hands visible, mid-stitch. Needle pulls thread through sock fabric.
2. **Frame 60-120 (2-4s):** Another stitch. The cross-hatch pattern grows. Practiced, rhythmic.
3. **Frame 120-150 (4-5s):** Final stitch of a pass. Thread pulled taut. The repair looks clean.
4. **Frame 150-180 (5-6s):** Hold. Hands pause briefly. The work is neat.

### Typography
- None (pure B-roll)

### Easing
- Natural video — no programmatic easing

### Veo Prompt

```
Medium-close shot of an elderly woman's hands carefully darning a dark wool sock by warm amber lamplight. A darning needle pulls thread through the fabric in a practiced cross-hatch pattern over a small hole. A wooden darning mushroom is visible inside the sock. Warm incandescent lamplight from camera-right illuminates the hands and work. Shallow depth of field with a soft warm background suggesting a 1950s living room with an upholstered chair. Slightly elevated camera angle looking down at the hands. Static camera, no movement. Warm amber color grade, nostalgic but naturalistic. 24fps with subtle film grain. The mood is quiet domestic skill and patience.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."
> "...you're getting really good at this."

Segments: `cold_open_001`, `cold_open_002`

- **0:00**: Hands darning, mid-stitch
- **3.46s** ("you're getting really good at this"): Stitch finishes — repair looks clean

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="grandmother_darning"
    src="/clips/grandmother_darning.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning",
  "camera": {
    "framing": "medium_close_hands_and_sock",
    "movement": "static",
    "dof": "shallow",
    "aperture": "f/2.0",
    "angle": "slightly_elevated_15deg"
  },
  "lighting": {
    "key": { "color": "#F5D6A8", "position": "camera_right_lamp", "type": "incandescent" },
    "fill": { "color": "#3D2B1A", "opacity": 0.15, "type": "ambient" },
    "grade": "warm_amber_nostalgic"
  },
  "props": ["dark_wool_sock", "darning_needle", "thread", "wooden_darning_mushroom"],
  "narrationSegments": ["cold_open_001", "cold_open_002"],
  "narrationTimingSeconds": { "start": 0, "end": 5 }
}
```

---
