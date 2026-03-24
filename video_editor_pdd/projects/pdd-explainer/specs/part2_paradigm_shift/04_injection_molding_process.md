[veo:]

# Section 2.4: Injection Molding Process — Liquid Into Mold

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:59 - 1:07

## Visual Description

A cinematic close-up of the injection molding process in action. Liquid plastic flows into a precision mold — the mold is visible in cross-section or through a transparent viewport. The mold walls are precise, hard-edged, defining an exact shape. The liquid fills the cavity, conforming perfectly to the walls.

The camera is tight on the action — this is the mechanical poetry of the process. The mold opens and a perfect plastic part ejects cleanly. The focus is on the precision of the mold walls and how the material conforms to them.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Interior of injection molding machine
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on the mold cavity and injection point
- Movement: Slow pan across the mold surface, then hold as part ejects
- Depth of field: Shallow, f/2.8 — mold walls sharp, background soft
- Angle: Slightly elevated, looking down into the mold cavity

**Lighting**
- Key light: Warm industrial `#FFD699` — the glow of heated plastic
- Fill: Cool blue-white from overhead `#B8C9E0` at 0.3
- Rim: Edge highlight on polished mold walls `#C0C0C0` at 0.4
- Hot plastic glow: `#FF8C42` at 0.2 on the molten material

**Subject**
- Mold: Precision-machined steel, polished surfaces catching light
- Liquid plastic: Flowing into the cavity, warm amber/orange tone
- Ejected part: Clean, perfect, industrial precision

### Animation Sequence
1. **Frame 0-120 (0-4s):** Close-up on liquid plastic flowing into the mold cavity. The walls of the mold are clearly visible as hard constraints.
2. **Frame 120-240 (4-8s):** The mold opens. A perfect plastic part ejects smoothly. Clean, precise, identical to the mold shape.

### Typography
- None (pure B-roll footage)

### Easing
- Camera pan: natural, steady
- Hard cut in and out

### Veo Prompt

```
Extreme close-up of an injection molding machine in operation. Molten amber-orange plastic flows into a precision steel mold cavity. The polished mold walls gleam under warm industrial lighting, defining a precise geometric shape. Shallow depth of field with the mold surface razor-sharp and the background softly blurred. The camera holds steady as the plastic fills the cavity. Warm industrial lighting with cool blue fill from overhead. Cinematic, 24fps, macro-photography style. The mood is mechanical precision — material conforming perfectly to engineered constraints.
```

## Narration Sync
> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."
> "Make the mold once. Produce unlimited identical parts. Refine the mold once, every future part improves automatically."

Segments: `part2_paradigm_shift_006`, `part2_paradigm_shift_007`

- **0:59** ("Before it existed"): Liquid plastic flows into mold
- **1:04** ("Make the mold once"): Part ejects — production in action

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="injection_molding_process"
    src="/clips/injection_molding_process.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "injection_molding_process",
  "camera": {
    "framing": "extreme_close_up",
    "movement": "slow_pan_then_hold",
    "dof": "shallow",
    "aperture": "f/2.8",
    "angle": "slightly_elevated"
  },
  "lighting": {
    "key": { "color": "#FFD699", "type": "warm_industrial" },
    "fill": { "color": "#B8C9E0", "opacity": 0.3, "type": "overhead_cool" },
    "rim": { "color": "#C0C0C0", "opacity": 0.4, "type": "mold_edge_highlight" },
    "materialGlow": { "color": "#FF8C42", "opacity": 0.2, "type": "molten_plastic" }
  },
  "narrationSegments": ["part2_paradigm_shift_006", "part2_paradigm_shift_007"]
}
```

---
