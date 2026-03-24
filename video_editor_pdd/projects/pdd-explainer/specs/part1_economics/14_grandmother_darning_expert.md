[veo:]

# Section 1.14: Grandmother Darning Expert — Companion Veo Clip

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 5:20 - 5:28

## Visual Description

A close-up of an elderly woman's hands expertly darning a wool sock under warm lamplight. The hands are weathered and skilled — this is someone who has done this a thousand times. A darning mushroom or egg sits beneath the sock. The needle moves with practiced precision, weaving thread across the hole in a neat crosshatch pattern.

The lighting is warm amber from a single table lamp, creating dramatic but gentle shadows. The setting is domestic and cozy — a reading chair, perhaps a small table with a sewing kit. The color palette is warm, nostalgic, but the focus is on competence, not sentimentality.

This clip is embedded within the right panel of 12_developer_darning_split.md.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Domestic interior, warm lamplight dominant
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up (CU) on hands, sock, needle, and darning mushroom
- Movement: static, locked-off — observational
- Depth of field: moderate, f/2.8 — hands sharp, background soft
- No drift or push-in

**Lighting**
- Key light: warm amber `#D4A043`, single table lamp, upper-left
- Fill: minimal — natural shadow play
- Subtle rim light on needle from lamp reflection
- Overall tone: warm, intimate, amber

**Subject**
- Elderly woman's hands — weathered, skilled
- Wool sock stretched over a darning mushroom
- Darning needle with thread, weaving crosshatch pattern
- Small sewing basket or kit visible at edge of frame

**Key Moments**
- 0-4s: Needle moves in steady rhythm, threading through the weave. Expert precision.
- 4-8s: Pull thread tight. Brief pause to examine work. Resume with satisfaction.

### Animation Sequence
1. **Frame 0-120 (0-4s):** Hands darning in steady rhythm. Needle weaves back and forth across the hole.
2. **Frame 120-180 (4-6s):** Thread pulled tight. Brief pause — hands hold the sock up slightly to inspect.
3. **Frame 180-240 (6-8s):** Resume darning. The work is meditative and skilled.

### Typography
- None (pure B-roll footage)

### Easing
- Fade-in: `easeOut(quad)`, 0.5s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Close-up of an elderly woman's weathered hands expertly darning a wool sock stretched over a darning mushroom. A darning needle weaves thread in a neat crosshatch pattern across a hole. Warm amber lamplight from a single table lamp at upper-left creates gentle shadows. Moderate depth of field, f/2.8, hands sharp, background soft. Domestic interior with a reading chair visible. Small sewing basket at edge of frame. Static locked-off camera, no movement. Warm intimate amber tone. The work is skilled and practiced. Cinematic, 24fps, warm color grade.
```

## Narration Sync

> "Tools like Cursor and Claude Code are the best darning needles ever made."

Segment: `part1_economics_032`
Timing: 5:20 - 5:28 (embedded in right panel of 12_developer_darning_split)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="grandmother_darning_expert"
    src="/clips/grandmother_darning_expert.mp4"
    fit="cover"
  />
  <Sequence from={0} durationInFrames={15}>
    <FadeIn />
  </Sequence>
  <Sequence from={230} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "grandmother_darning_expert",
  "camera": {
    "framing": "close_up",
    "movement": "static",
    "dof": "moderate",
    "drift": false
  },
  "lighting": {
    "key": { "color": "#D4A043", "position": "upper_left", "type": "table_lamp" },
    "fill": "minimal",
    "grade": "warm_amber"
  },
  "characters": [
    {
      "id": "grandmother_darner",
      "label": "Grandmother",
      "referencePrompt": "Elderly woman with weathered skilled hands, domestic setting, warm lamplight"
    }
  ],
  "embeddedIn": "12_developer_darning_split",
  "panel": "right",
  "narrationSegments": ["part1_economics_032"],
  "narrationTimingSeconds": { "start": 441.12, "end": 447.88 }
}
```

---
