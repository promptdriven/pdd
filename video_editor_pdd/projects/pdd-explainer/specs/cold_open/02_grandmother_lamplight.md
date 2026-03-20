[veo:]

# Section 0.2: Grandmother Lamplight — Darning by Warm Light

**Tool:** Veo (cinematic B-roll)
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:00 - 0:08 (embedded in split screen, full clip length ~10s)

## Visual Description

Close-up cinematic footage of an elderly woman's hands darning a wool sock under warm lamplight. The setting is a 1950s living room — a wooden side table, a ceramic lamp casting a golden cone of light, a wicker sewing basket with spools of thread. The grandmother sits in a floral armchair, the sock stretched over a smooth wooden darning egg. Her fingers are practiced and sure: she weaves the needle through the worn fabric, pulling thread in even, rhythmic strokes. The camera holds a tight medium close-up on her hands and the sock, with shallow depth of field softening the background into warm bokeh circles. Period-accurate details: cotton housedress, simple wedding band, reading glasses perched on her nose.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Aspect ratio: 16:9 native (no letterboxing)
- Color temperature: 3200K warm tungsten

### Chart/Visual Elements
- **Subject:** Elderly woman's hands, wool sock on darning egg
- **Lighting:** Single warm practical lamp (key), soft ambient fill from screen-left
- **Depth of field:** Shallow — f/2.8 equivalent, focus on hands/needle
- **Camera:** Static or micro-drift (< 2px/s), locked on hands
- **Palette:** Warm amber `#D4A043`, cream `#F5E6C8`, deep brown `#3B2F1A`
- **Film grain:** Light grain consistent with period aesthetic

### Animation Sequence
1. **Frame 0-60 (0-2s):** Camera fades in on hands already mid-stitch. Needle pulls through fabric.
2. **Frame 60-150 (2-5s):** Grandmother turns the sock slightly on the darning egg. Makes two more passes. Thread catches the lamplight.
3. **Frame 150-240 (5-8s):** She ties off the final stitch, holds the sock up briefly to inspect her work. Satisfied.
4. **Frame 240-300 (8-10s):** She lowers the sock to her lap. Reaches for another garment from the basket. The cycle continues.

### Typography
- None — pure cinematic footage

### Easing
- Camera micro-drift: `linear` — imperceptible slow movement

### Veo Prompt
```
Cinematic close-up of an elderly woman's hands darning a wool sock by lamplight in a 1950s living room. She sits in a floral armchair with a wooden darning egg, weaving a needle through worn fabric with practiced, rhythmic strokes. Warm tungsten lighting from a ceramic table lamp creates golden highlights on her hands and the wool thread. Shallow depth of field with soft bokeh in the background. Wicker sewing basket visible beside her. Period-accurate details: cotton housedress, simple wedding band, reading glasses. Film-like grain. Camera holds a steady medium close-up with minimal movement. Warm color palette, nostalgic tone. 16:9, cinematic.
```

## Narration Sync
> "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."

(This clip plays in the RIGHT panel of the split screen during cold_open_001 and cold_open_002.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <VeoClip
    clipId="grandmother_darning"
    src="/assets/veo/grandmother_darning.mp4"
    startFrom={0}
    playbackRate={1}
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning",
  "duration": 10,
  "frames": 300,
  "camera": "static_close_up",
  "colorTemperature": "3200K",
  "era": "1950s",
  "characters": [
    {
      "id": "grandmother",
      "label": "Great-Grandmother",
      "referencePrompt": "Elderly woman in her 70s, silver hair in a low bun, wire-rimmed reading glasses, cotton floral housedress, simple gold wedding band, gentle weathered hands. Warm and practiced demeanor."
    }
  ],
  "setting": "1950s_living_room",
  "props": ["darning_egg", "wool_sock", "ceramic_lamp", "sewing_basket"],
  "narrationSegments": ["cold_open_001", "cold_open_002"]
}
```
