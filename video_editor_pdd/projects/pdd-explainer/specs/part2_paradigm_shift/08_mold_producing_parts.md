[veo:]

# Section 2.8: Mold Producing Parts — Disposable Plastic, Permanent Mold

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:24 - 1:32

## Visual Description

A cinematic close-up of an injection mold producing a plastic part. The steel mold is the visual hero — polished, precise, engineered. Liquid plastic flows into the cavity, fills the precise shape defined by the mold walls, and a finished part ejects. The emphasis is on the mold's permanence contrasted with the part's disposability.

The lighting emphasizes the mold's machined surfaces — cool industrial tones with warm highlights from the molten material. The mold is permanent, substantial, engineered. The plastic part is just output.

This clip is used as the RIGHT panel in the `06_craftsman_vs_mold` split composition.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Industrial machine interior
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on the mold cavity — steel walls visible, plastic filling the shape
- Movement: Near-static, slight settle — the mold doesn't move, the material moves
- Depth of field: Moderate, f/4 — mold walls sharp, machine background soft
- Angle: Slightly elevated, looking into the cavity

**Lighting**
- Key light: Cool industrial overhead `#D4E5F7`
- Fill: Warm glow from molten plastic `#FF8C42` at 0.2
- Rim: Specular highlights on polished steel `#C0C0C0` at 0.5
- Overall tone: Cool precision with warm material contrast

**Subject**
- Mold: Precision steel, polished machined surfaces. The hero of the shot.
- Plastic: Warm amber-orange liquid filling a geometric cavity
- Ejected part: Clean, precise, but clearly secondary to the mold

### Animation Sequence
1. **Frame 0-120 (0-4s):** Liquid plastic flows into the mold cavity. The steel walls gleam. The material conforms perfectly to the shape.
2. **Frame 120-240 (4-8s):** The mold opens slightly and a perfect part is visible. The mold's surface dominates the frame — permanent, engineered, the true object of value.

### Typography
- None (pure B-roll footage)

### Easing
- Camera movement: near-static, subtle settle
- Hard cut in and out (used within split composition)

### Veo Prompt

```
Close-up shot of a precision steel injection mold with polished machined surfaces. Warm amber-orange molten plastic flows into the geometric cavity, conforming precisely to the steel walls. Cool industrial overhead lighting with specular highlights gleaming off the polished metal surfaces. Warm glow radiates from the molten material. Near-static camera with very subtle movement. Moderate depth of field with the mold walls in sharp focus. The mold is the visual hero — permanent, engineered, substantial. Cinematic, 24fps. The mood is industrial precision and permanence.
```

## Narration Sync
> "In molding, value lives in the specification — the mold. The plastic part? Disposable. Regenerate it at will."

Segment: `part2_paradigm_shift_012`

- **1:24** ("In molding"): Mold visible, plastic flowing
- **1:28** ("Disposable"): Part visible but secondary to the mold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="mold_producing_parts"
    src="/clips/mold_producing_parts.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "mold_producing_parts",
  "camera": {
    "framing": "close_up_cavity",
    "movement": "near_static",
    "dof": "moderate",
    "aperture": "f/4",
    "angle": "slightly_elevated"
  },
  "lighting": {
    "key": { "color": "#D4E5F7", "type": "industrial_overhead" },
    "fill": { "color": "#FF8C42", "opacity": 0.2, "type": "molten_plastic_glow" },
    "rim": { "color": "#C0C0C0", "opacity": 0.5, "type": "steel_specular" },
    "grade": "cool_precision"
  },
  "usedIn": "06_craftsman_vs_mold (right panel)",
  "narrationSegments": ["part2_paradigm_shift_012"]
}
```

---
