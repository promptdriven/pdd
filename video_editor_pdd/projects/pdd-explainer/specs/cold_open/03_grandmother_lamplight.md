[veo:]

# Section 0.3: Grandmother by Lamplight — The Craft

**Tool:** Veo
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:08 - 0:13

## Visual Description

A close-up of elderly weathered hands darning a wool sock by warm amber lamplight. This is the emotional grounding shot for the entire video's metaphor. The grandmother's hands move with practiced precision — pulling thread through wool stretched over a wooden darning egg. The shallow depth of field isolates her hands against a softly blurred background of warm domestic interior.

The camera executes a slow push-in, tightening from a medium close-up to an extreme close-up on the needle entering the wool. Every detail matters: the texture of weathered skin, the glint of lamplight on the needle, the weave of the wool. This is genuine skilled craft — the shot is intimate and respectful, not nostalgic or diminishing.

This clip intercuts with the zoom-out in spec 02, providing the live-action emotional texture underneath the Remotion animation on the right panel.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Domestic interior, warm amber lamplight
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium close-up → Extreme close-up (hands only)
- Movement: Slow push-in, ~12% travel over 5 seconds
- Depth of field: shallow, f/1.8 — hands sharp, everything else creamy bokeh
- Angle: slightly overhead, looking down at lap-level work

**Lighting**
- Key light: warm amber lamplight `#E8A040`, positioned upper-left — a single practical lamp source
- Fill: minimal — deep shadows on the right side of hands
- Rim: faint warm edge light catching the top of the needle and thread
- Overall tone: Rembrandt-warm, shadows pushed toward `#1A0E04`
- Lamp glow: visible in upper-left bokeh as a soft amber orb

**Subject**
- Elderly woman's hands — weathered, capable, relaxed
- Wooden darning egg visible beneath the sock — warm wood tone
- Wool sock: dark gray with a visible hole being closed by neat crosshatch stitches
- Needle: steel, catching lamplight
- Thread: cream-colored darning wool

**Key Moments**
- 0-1.5s: Medium close-up. Hands pull thread through, needle glinting. Steady rhythm.
- 1.5-3s: Push-in begins. Frame tightens on the point where needle enters wool.
- 3-4.5s: Extreme close-up. The crosshatch pattern of the darn is visible — tiny parallel threads woven together.
- 4.5-5s: Thread pulled taut. Hold.

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in from black. Amber warmth fills the frame.
2. **Frame 15-45 (0.5-1.5s):** Medium close-up. Hands work steadily. Needle catches light.
3. **Frame 45-90 (1.5-3s):** Slow push-in. Frame tightens. Background blurs further.
4. **Frame 90-135 (3-4.5s):** Extreme close-up. The weave of the darn is visible. Individual threads distinguishable.
5. **Frame 135-150 (4.5-5s):** Thread pulls taut. Hold. Begin fade-out.

### Typography
- None (pure B-roll footage)

### Easing
- Push-in: `linear` (smooth, mechanical dolly feel)
- Fade-in: `easeOut(quad)`, 0.5s
- Fade-out: `easeIn(quad)`, 0.5s

### Veo Prompt

```
Extreme close-up of elderly weathered hands darning a dark gray wool sock by warm amber lamplight. A wooden darning egg is visible beneath the sock. A steel needle pulls cream-colored darning wool through the fabric in neat crosshatch stitches. Slow push-in camera movement from medium close-up to extreme close-up. Shallow depth of field, f/1.8, background is creamy bokeh of a warm domestic interior. Single warm amber lamp source from upper left, Rembrandt-style lighting with deep shadows. Intimate, respectful, showing genuine skilled craft. The hands are steady and practiced. Cinematic, 24fps, warm amber color grade, film grain.
```

## Narration Sync

> "But here's what your great-grandmother figured out sixty years ago."

Segment: `cold_open_002` (intercut with 02_zoom_out_accumulated)
Timing: 0:08 - 0:13 (plays underneath / intercuts with the Remotion zoom-out on the right panel)

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={150}>
  <VeoClip
    clipId="grandmother_darning_lamplight"
    src="/clips/grandmother_darning_lamplight.mp4"
    fit="cover"
  />
  {/* Fade in */}
  <Sequence from={0} durationInFrames={15}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={135} durationInFrames={15}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning_lamplight",
  "camera": {
    "framing": "medium_closeup_to_extreme_closeup",
    "movement": "push_in",
    "travelPercent": 12,
    "dof": "shallow",
    "angle": "slightly_overhead"
  },
  "lighting": {
    "key": { "color": "#E8A040", "position": "upper_left", "type": "practical_lamp" },
    "fill": "minimal",
    "rim": "warm_edge",
    "grade": "rembrandt_warm"
  },
  "characters": [
    {
      "id": "grandmother",
      "label": "Great-Grandmother",
      "referencePrompt": "Elderly woman, 70s-80s, weathered hands with visible age spots, wearing a dark cardigan. Warm domestic setting, 1950s era. Skilled and practiced with needle and thread."
    }
  ],
  "intercutWith": "02_zoom_out_accumulated",
  "panel": "right",
  "narrationSegments": ["cold_open_002"],
  "narrationTimingSeconds": { "start": 8.0, "end": 13.0 }
}
```

---
