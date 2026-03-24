[veo:]

# Section 2.9: 1980s Chip Lab — Hand-Drawing Circuits

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:50 - 1:58

## Visual Description

A cinematic scene of a 1980s electronics lab. An engineer hunches over a large drafting desk, drawing circuits by hand on a paper schematic. The desk is covered with technical drawings — transistor symbols, resistor networks, wire traces filling the page. The engineer uses a mechanical pencil and a ruler, carefully connecting components.

The environment is period-accurate: fluorescent tube lighting, oscilloscopes in the background, large paper schematics pinned to walls, coffee mug, reference manuals. The mood is skilled labor approaching its limit — the drawings are becoming impossibly dense.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: 1980s electronics lab interior
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium shot from over-the-shoulder, looking down at the schematic
- Movement: Very slow drift from the engineer toward the paper, revealing density
- Depth of field: Moderate, f/3.5 — paper surface sharp, background instruments soft
- Angle: Elevated, looking down over the engineer's shoulder

**Lighting**
- Key light: Overhead fluorescent tubes `#F5F5DC` — flat, institutional
- Fill: Warm desk lamp `#FFD699` at 0.3 — focused on the schematic
- Accent: Green CRT glow from oscilloscope in background `#00FF41` at 0.05
- Overall tone: 1980s institutional, warm paper, cool fluorescent

**Subject**
- Engineer: Male, 30s-40s, wearing short-sleeve button-down shirt. Period-appropriate.
- Action: Drawing circuit connections with mechanical pencil. Focused, methodical.
- Desk: Covered with schematics, transistor symbols dense across large paper sheets
- Background: Oscilloscopes, lab equipment, pinned schematics on wall

### Animation Sequence
1. **Frame 0-120 (0-4s):** Over-shoulder medium shot. Engineer's hand moves across the schematic, drawing a transistor connection. The density of existing drawings is visible.
2. **Frame 120-240 (4-8s):** Camera drifts closer to the paper. Hundreds of transistor symbols fill the view. The hand slows — the complexity is overwhelming.

### Typography
- None (pure B-roll footage)

### Easing
- Camera drift: natural, slow dolly forward
- Hard cut in and out

### Veo Prompt

```
Over-the-shoulder medium shot of an electronics engineer in a 1980s laboratory, hunched over a large drafting desk drawing circuits by hand with a mechanical pencil. Dense transistor symbols, resistor networks, and wire traces fill a large paper schematic. Short-sleeve button-down shirt, 1980s period style. Overhead fluorescent tube lighting with a warm desk lamp illuminating the schematic. An oscilloscope with a green CRT display glows softly in the background. Camera slowly drifts forward from over the shoulder toward the paper, revealing the overwhelming density of hand-drawn components. Moderate depth of field. Cinematic, 24fps. The mood is skilled labor approaching its limits — methodical work becoming impossibly complex.
```

## Narration Sync
> "And it's not just plastics. The chip industry hit this exact wall, and I watched it happen."
> "In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up."

Segments: `part2_paradigm_shift_013`, `part2_paradigm_shift_014`

- **1:50** ("not just plastics"): 1980s lab establishing shot, engineer drawing
- **1:57** ("chip designers drew every gate"): Camera closer, density overwhelming

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="1980s_chip_lab"
    src="/clips/1980s_chip_lab.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "1980s_chip_lab",
  "camera": {
    "framing": "over_shoulder_medium",
    "movement": "slow_drift_forward",
    "dof": "moderate",
    "aperture": "f/3.5",
    "angle": "elevated_over_shoulder"
  },
  "lighting": {
    "key": { "color": "#F5F5DC", "type": "overhead_fluorescent" },
    "fill": { "color": "#FFD699", "opacity": 0.3, "type": "desk_lamp" },
    "accent": { "color": "#00FF41", "opacity": 0.05, "type": "oscilloscope_crt" },
    "grade": "1980s_institutional"
  },
  "characters": [
    {
      "id": "chip_engineer",
      "label": "1980s Chip Engineer",
      "referencePrompt": "Electronics engineer, male, 30s-40s, short-sleeve button-down shirt, 1980s style. Hunched over drafting desk drawing circuits with mechanical pencil under fluorescent lighting."
    }
  ],
  "narrationSegments": ["part2_paradigm_shift_013", "part2_paradigm_shift_014"]
}
```

---
