[veo:]

# Section 2.7: Craftsman Carving — Hand-Carved Wooden Chair

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:24 - 1:32

## Visual Description

A cinematic close-up of a craftsman's hands carving a wooden chair leg on a workbench. Wood shavings curl away from a sharp chisel. The grain of the wood is visible — each cut permanent, each decision irreversible. The lighting is warm workshop amber — late afternoon light through dusty windows.

The emphasis is on permanence and accumulation: you can see the history of every cut in the wood. The craftsman is skilled, deliberate, careful. This is beautiful work — but each mark is forever.

This clip is used as the LEFT panel in the `06_craftsman_vs_mold` split composition.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Warm wood workshop
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Close-up on hands and chisel, with chair leg and workbench visible
- Movement: Very slow drift, almost static — stability emphasizes permanence
- Depth of field: Moderate, f/3.5 — hands and chisel sharp, background soft
- Angle: Eye-level, slightly angled to show the cut and the wood grain

**Lighting**
- Key light: Warm afternoon sun through window `#FFD699`
- Fill: Warm ambient from workshop `#8B6914` at 0.15
- Rim: Golden edge light on wood shavings `#DAA520` at 0.2
- Overall tone: Warm, nostalgic, artisanal

**Subject**
- Craftsman: Experienced hands, possibly older. Worn workshop apron.
- Action: Steady chisel strokes removing thin curls of wood from a chair leg
- Material: Rich hardwood with visible grain — oak or walnut tones

### Animation Sequence
1. **Frame 0-120 (0-4s):** Close-up on chisel meeting wood. A curl of wood shaving rises. The grain catches the light.
2. **Frame 120-240 (4-8s):** The craftsman repositions slightly and makes another deliberate cut. The accumulation of marks is visible on the workpiece.

### Typography
- None (pure B-roll footage)

### Easing
- Camera drift: near-static, very subtle micro-movement
- Hard cut in and out (used within split composition)

### Veo Prompt

```
Close-up shot of a craftsman's weathered hands carefully carving a wooden chair leg with a sharp chisel on a sturdy workbench. Thin curls of wood shavings rise from each deliberate stroke. Rich hardwood grain visible in warm oak tones. Late afternoon golden sunlight streams through dusty workshop windows, casting warm amber light across the scene. Shallow depth of field, the chisel edge and wood surface razor-sharp. Nearly static camera with very subtle micro-movement. The mood is skilled permanence — every cut is irreversible, every mark accumulates. Cinematic, 24fps.
```

## Narration Sync
> "In crafting, value lives in the object. You protect the object. Losing the chair is losing everything."

Segment: `part2_paradigm_shift_011`

- **1:24** ("In crafting"): Chisel meets wood, curling shaving
- **1:28** ("Losing the chair"): Accumulated marks visible on the workpiece

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="craftsman_carving"
    src="/clips/craftsman_carving.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "craftsman_carving",
  "camera": {
    "framing": "close_up_hands",
    "movement": "near_static",
    "dof": "moderate",
    "aperture": "f/3.5",
    "angle": "eye_level"
  },
  "lighting": {
    "key": { "color": "#FFD699", "type": "afternoon_sun" },
    "fill": { "color": "#8B6914", "opacity": 0.15, "type": "workshop_ambient" },
    "rim": { "color": "#DAA520", "opacity": 0.2, "type": "shaving_edge_light" },
    "grade": "warm_artisanal"
  },
  "usedIn": "06_craftsman_vs_mold (left panel)",
  "narrationSegments": ["part2_paradigm_shift_011"]
}
```

---
