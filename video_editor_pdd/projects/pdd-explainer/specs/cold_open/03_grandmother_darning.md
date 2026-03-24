[veo:]

# Section 0.3: Grandmother Darning — 1950s Lamplight Mending

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:00 - 0:06

## Visual Description

A cinematic close-up of an elderly woman's hands carefully darning a wool sock by warm lamplight. The setting is a 1950s domestic interior — wooden chair, side table with a kerosene or incandescent lamp, a sewing basket nearby. The hands are weathered but deft, threading a darning needle through stretched wool fabric over a darning egg.

The lighting is warm amber from the lamp, creating deep shadows and a cozy, intimate atmosphere. The mood is quiet skill and patience — this is someone who has done this a thousand times. The sock patch finishes neatly, thread pulled taut.

This clip is used as the RIGHT panel in the `01_split_screen_hook` split composition.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: 1950s domestic interior — warm, wood tones
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on hands darning, wool sock stretched over darning egg
- Movement: Very slow push-in, almost imperceptible — draws the viewer closer
- Depth of field: Very shallow, f/1.8 — hands and needle sharp, background softly blurred
- Angle: Slightly elevated, looking down at the work in the lap

**Lighting**
- Key light: Warm amber lamplight `#D9944A`, from a table lamp at frame right
- Fill: Faint ambient room light `#2A1F14` at 0.08 — dark room, lamp is primary source
- Rim: None — single-source lighting for period authenticity
- Overall tone: Warm, golden, nostalgic — high contrast with deep shadows

**Subject**
- Great-grandmother: Elderly woman, 70s-80s, weathered hands with visible age spots
- Action: Threading darning needle through wool sock, pulling thread taut, finishing a neat patch
- Props: Darning egg (wooden), wool sock with visible wear, darning needle, thread
- Setting details: Wooden chair arm visible, sewing basket with thread spools

### Animation Sequence
1. **Frame 0-60 (0-2s):** Close-up on hands. Needle pushes through wool. Lamp flickers faintly.
2. **Frame 60-120 (2-4s):** Thread pulled through. Neat cross-stitch pattern forming over the hole.
3. **Frame 120-180 (4-6s):** Final stitch. Thread pulled taut. The patch is complete — clean, careful work.

### Typography
- None (pure B-roll footage)

### Easing
- Camera push-in: natural, barely perceptible — `easeInOut(sine)` equivalent
- Hard cut in and out (used within split composition)

### Veo Prompt

```
Extreme close-up of elderly weathered hands darning a wool sock over a wooden darning egg. Warm amber lamplight from a single table lamp illuminates the scene, casting deep shadows. 1950s domestic interior setting — wooden furniture, sewing basket visible in soft background blur. The needle threads through stretched wool fabric in a careful cross-stitch pattern. Very shallow depth of field, f/1.8. Warm golden color grade, nostalgic tone. Very slow push-in camera movement. Cinematic, 24fps, subtle film grain. The mood is quiet patience and practiced skill.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot..."

Segment: `cold_open_001`

- **0:00** ("If you use Cursor"): Hands darning, needle pushing through wool
- **0:02** ("Claude Code"): Thread being pulled through
- **0:04** ("Copilot"): Patch nearing completion

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="grandmother_darning"
    src="/clips/grandmother_darning.mp4"
    fit="cover"
  />
  {/* Warm color grade overlay — enhance amber tone */}
  <ColorGrade color="#D9944A" opacity={0.04} />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning",
  "camera": {
    "framing": "extreme_close_up_hands",
    "movement": "very_slow_push_in",
    "dof": "very_shallow",
    "aperture": "f/1.8",
    "angle": "slightly_elevated"
  },
  "lighting": {
    "key": { "color": "#D9944A", "position": "frame_right_lamp", "type": "lamplight" },
    "fill": { "color": "#2A1F14", "opacity": 0.08, "type": "ambient" },
    "rim": "none",
    "grade": "warm_golden_nostalgic"
  },
  "characters": [
    {
      "id": "grandmother",
      "label": "Great-Grandmother",
      "referencePrompt": "Elderly woman in her 70s-80s, weathered hands with visible age spots, seated in a wooden chair. 1950s domestic attire. Lit by warm amber lamplight. Darning a wool sock over a wooden darning egg."
    }
  ],
  "props": ["darning_egg", "wool_sock", "darning_needle", "sewing_basket"],
  "usedIn": "01_split_screen_hook (right panel)",
  "narrationSegments": ["cold_open_001"]
}
```

---
