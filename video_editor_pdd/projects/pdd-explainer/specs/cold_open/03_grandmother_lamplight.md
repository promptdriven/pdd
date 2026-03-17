[veo:]

# Section 0.3: Grandmother by Lamplight — The Craft of Darning

**Tool:** Veo
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:08 - 0:13

## Visual Description

A cinematic B-roll insert that runs under the narration, intercut with the Remotion zoom-out sequence. Close-up of weathered hands carefully threading a darning needle through a wool sock, lit by warm amber lamplight. The shot is intimate, respectful — this is skilled work. The hands move with decades of practiced precision.

The camera slowly pushes in on the hands, soft focus on the background. Warm amber light catches the thread as it pulls through the weave. The sock is stretched over a wooden darning egg. A slight camera drift gives the shot a handheld documentary feel.

This clip provides the emotional grounding for the metaphor — darning as genuine craft, not waste. The audience should feel the skill before they understand the economics.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Warm interior, low-key lighting
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Extreme close-up (ECU) on hands and sock
- Push-in: subtle, ~5% zoom over 5 seconds
- Depth of field: shallow, f/2.0 equivalent — hands sharp, background soft
- Drift: slight handheld wobble, 2-3px per second

**Lighting**
- Key light: warm amber #D4A043, positioned upper-left (practical lamp)
- Fill: minimal, deep shadows on right side
- Thread highlight: specular glint as thread catches light mid-pull
- Overall tone: warm sepia grade, shadows pushed toward #1A1308

**Subject**
- Elderly woman's hands, weathered, steady
- Darning needle: steel, glinting
- Wool sock: muted oatmeal #C4956A, stretched over wooden darning egg
- Thread: amber #D4A043, taut

### Animation Sequence

1. **Frame 0-30 (0-1.0s):** Shot fades in from black. Hands visible, needle mid-stitch. Lamplight flickers subtly.
2. **Frame 30-90 (1.0-3.0s):** Two complete darning stitches. Thread pulls through weave with visible tension. Camera pushes in slowly.
3. **Frame 90-120 (3.0-4.0s):** Thread catches lamplight — brief specular highlight. Hands pause, inspect the work.
4. **Frame 120-150 (4.0-5.0s):** Hands settle. Needle rests against sock. Hold on the completed repair. Fade begins at frame 140.

### Typography

- None (pure B-roll footage)

### Easing

- Camera push-in: `linear` (smooth mechanical tracking)
- Fade-in: `easeOut(quad)`, 1s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Extreme close-up of elderly woman's weathered hands darning a wool sock by warm amber lamplight. The sock is stretched over a wooden darning egg. A steel needle pulls thread through the weave with practiced precision. Shallow depth of field, f/2.0. Warm amber key light from a practical table lamp upper-left, deep shadows on the right. Slow push-in. The thread catches the light briefly as it's pulled taut. 1950s domestic interior, intimate and respectful. Cinematic, 24fps, warm color grade.
```

## Narration Sync

> "But here's what your great-grandmother figured out sixty years ago."
Segment: `cold_open_003`
Timing: 0:08 - 0:13 (intercut with 02_zoom_out_accumulated)

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={150}>
  <VeoClip
    clipId="grandmother_lamplight"
    src="/clips/grandmother_lamplight.mp4"
    fit="cover"
  />
  {/* Fade in */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={140} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "grandmother_lamplight",
  "characters": [
    {
      "id": "grandmother",
      "label": "Grandmother",
      "referencePrompt": "Elderly woman with weathered hands, 1950s domestic setting, warm amber lamplight, darning wool socks with practiced skill"
    }
  ],
  "camera": {
    "framing": "extreme_close_up",
    "movement": "push_in",
    "zoomPercent": 5,
    "dof": "shallow",
    "drift": true
  },
  "lighting": {
    "key": { "color": "#D4A043", "position": "upper_left", "type": "practical_lamp" },
    "fill": "minimal",
    "grade": "warm_sepia"
  },
  "narrationSegments": ["cold_open_003"],
  "narrationTimingSeconds": { "start": 8.0, "end": 13.0 }
}
```

---
