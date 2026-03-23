[veo:]

# Section 0.3: Grandmother Darning — Companion Clip (Split RIGHT)

**Tool:** Veo
**Duration:** ~11s (338 frames @ 30fps)
**Timestamp:** 0:00 - 0:11

## Visual Description

Cinematic footage of a 1950s great-grandmother carefully darning a wool sock by warm lamplight. This clip plays in the RIGHT panel of the split screen (spec 01). The grandmother is skilled and unhurried — her hands move with decades of practiced precision, threading a darning needle through the heel of a wool sock stretched over a darning egg.

The first 8 seconds show the close, intimate act of darning. At the zoom-out phase (~6s), the camera pulls back to reveal a drawer or basket beside her containing dozens of carefully mended garments — socks, shirts, trousers — each bearing neat, visible patches. The accumulation is loving but enormous.

The lighting is warm amber from a nearby table lamp or oil lamp — a period-appropriate warm glow that contrasts with the developer's cool blue. The color palette is rich, warm, slightly golden, evoking nostalgia and craft.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: 1950s domestic interior — armchair, side table, lamp
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on hands → pull back to medium shot revealing drawer/basket
- Movement: Slow dolly-back/zoom-out starting at ~6s
- Depth of field: Moderate, f/2.8 — hands sharp, background warmly blurred initially
- Angle: Slightly above, looking down at the work in her lap

**Lighting**
- Key light: Warm amber lamp glow `#D9944A`, from frame-right table lamp
- Fill: Soft warm ambient `#2A1F14` at 0.2
- Rim: None — single-source period lighting
- Overall tone: Warm, golden, nostalgic — slightly heightened warmth

**Subject**
- Grandmother: elderly woman, 70s, silver hair, wearing period-appropriate house dress or cardigan
- Hands: wrinkled, skilled, holding darning needle and wool sock on darning egg
- Surroundings: 1950s domestic interior — wooden side table, fabric-shade lamp, patterned armchair

**Key Moments**
- 0-3s: Close-up on grandmother's hands darning. Needle passes through wool. Lamplight flickers.
- 3-6s: She finishes a patch. The sock is lifted slightly, inspected. Satisfaction in the gesture.
- 6-8s: Camera pulls back. A drawer or mending basket comes into view beside her, full of neatly mended garments.
- 8-11s: Wide enough to see the scale — dozens of mended items. Her hands rest on the completed sock. The weight of all that careful work is visible.

### Animation Sequence
1. **Frame 0-90 (0-3s):** Close-up on hands. Darning in progress. Warm amber light.
2. **Frame 90-180 (3-6s):** Patch finishes. Sock lifted and inspected.
3. **Frame 180-240 (6-8s):** Camera pulls back, revealing mending basket/drawer.
4. **Frame 240-338 (8-11s):** Hold on wide shot. Accumulated mending visible.

### Typography
- None (pure B-roll footage)

### Easing
- Hard cut in: instant
- Camera pull-back: natural in-camera dolly, smooth and unhurried
- Hold: static at final wide framing

### Veo Prompt

```
Close-up of an elderly woman's hands carefully darning a wool sock by warm lamplight. She is in her 70s with silver hair, seated in a 1950s domestic interior with a wooden side table and fabric-shade lamp. A darning needle threads through the heel of a grey wool sock stretched over a darning egg. Warm amber lamplight from frame-right illuminates her practiced hands. Slightly above camera angle looking down at her lap. Shallow depth of field, period-appropriate warm golden color grade. Cinematic, 24fps, subtle film grain. The mood is quiet domestic craftsmanship and accumulated skill.
```

## Narration Sync
> "If you use Cursor or Copilot or Claude Code, you're getting really good at darning socks."
> "Ah, but here's what your grandmother could have told you: the goal was never to get better at darning."

Segments: `cold_open_001`, `cold_open_002`, `cold_open_003`

- **0:00** ("If you use Cursor"): Grandmother darning, close-up on hands
- **0:03** ("really good"): She completes a patch — skill visible
- **0:05** ("darning socks"): Sock lifted, inspected — the parallel to the developer's completed edit
- **0:06** ("your grandmother"): Camera pulls back, drawer/basket revealed
- **0:09** ("the goal was never"): Wide shot, accumulated mending visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={338}>
  <VeoClip
    clipId="grandmother_darning"
    src="/clips/grandmother_darning.mp4"
    fit="cover"
  />
  <ColorGrade color="#D9944A" opacity={0.04} />
  <Vignette edgeColor="#1A0E00" edgeOpacity={0.2} />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning",
  "camera": {
    "framing": "close_up_to_medium_pullback",
    "movement": "slow_dolly_back",
    "dof": "moderate",
    "aperture": "f/2.8",
    "angle": "slightly_above_looking_down"
  },
  "lighting": {
    "key": { "color": "#D9944A", "position": "frame_right_lamp", "type": "warm_lamp" },
    "fill": { "color": "#2A1F14", "opacity": 0.2, "type": "ambient" },
    "rim": "none",
    "grade": "warm_golden_nostalgic"
  },
  "characters": [
    {
      "id": "grandmother",
      "label": "Great-Grandmother",
      "referencePrompt": "Elderly woman in her 70s, silver hair, wearing a 1950s house dress or cardigan. Warm lamplight illuminates her face and skilled hands. Seated in a period-appropriate armchair in a domestic interior."
    }
  ],
  "props": ["darning_needle", "wool_sock", "darning_egg", "mending_basket"],
  "narrationSegments": ["cold_open_001", "cold_open_002", "cold_open_003"],
  "parentSplit": "01_split_screen_hook",
  "panelPosition": "right"
}
```

---
