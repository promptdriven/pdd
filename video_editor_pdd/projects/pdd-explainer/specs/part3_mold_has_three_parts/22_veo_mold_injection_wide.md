[veo:]

# Section 3.22: Mold Injection Wide — Full Process B-Roll

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:20 - 1:28

## Visual Description

A cinematic wide shot of an industrial injection molding machine in operation. The camera captures the entire machine — the hopper, the injection barrel, the clamping unit, and the mold itself. The machine cycles once: the mold closes, material is injected (visible as a brief glow through translucent sections), the mold holds under pressure, then opens to reveal a perfectly formed part.

The lighting is dramatic — warm amber from the molten material contrasting with the cool industrial blues and grays of the machine. Steam or heat distortion is visible. The mood is mechanical precision and controlled power.

This B-roll provides visual variety during the ratchet-effect narration and grounds the metaphor in real-world manufacturing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Industrial factory floor, shallow depth of field
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Medium-wide shot of the injection molding machine
- Movement: Very slow dolly from left to right, tracking the injection cycle
- Depth of field: Medium, f/4.0 — machine sharp, background soft
- Angle: Slightly low angle, looking up at the machine for scale

**Lighting**
- Key: Cool industrial overhead `#B8C9E0` at 0.3
- Accent: Warm amber `#FFB347` from molten material, visible through mold seams
- Fill: Blue-gray ambient `#64748B` at 0.2
- Practical: Machine indicator lights, green `#4ADE80` and red `#EF4444`

**Subject**
- Industrial injection molding machine, mid-cycle
- Focus on the mold clamping and the brief moment of injection
- Clean, modern factory environment

### Animation Sequence
1. **Frame 0-120 (0-4s):** Machine visible. Mold closes with hydraulic precision. Clamping unit engages.
2. **Frame 120-240 (4-8s):** Injection occurs — brief amber glow through mold seams. Machine holds under pressure. The part is formed.

### Typography
- None (pure B-roll footage)

### Easing
- Camera dolly: natural, smooth
- Hard cut in and out

### Veo Prompt

```
Medium-wide shot of an industrial injection molding machine cycling in a modern factory. The camera slowly dollies from left to right. The mold clamps shut with hydraulic precision, and warm amber light glows briefly through the mold seams as material is injected. Cool industrial overhead lighting contrasts with the warm amber glow of molten material. Slightly low camera angle looking up at the machine. Shallow depth of field with the machine sharp against a soft factory background. Green and red indicator lights on the machine panel. Cinematic 24fps, industrial manufacturing aesthetic. The mood is mechanical precision and controlled power.
```

## Narration Sync
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise."

Segment: `part3_mold_has_three_parts_012`

- **1:20** ("ratchet effect"): Machine cycling, injection visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="mold_injection_wide"
    src="/clips/mold_injection_wide.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "mold_injection_wide",
  "camera": {
    "framing": "medium_wide",
    "movement": "slow_dolly_left_to_right",
    "dof": "medium",
    "aperture": "f/4.0",
    "angle": "slightly_low"
  },
  "lighting": {
    "key": { "color": "#B8C9E0", "opacity": 0.3, "type": "industrial_overhead" },
    "accent": { "color": "#FFB347", "type": "molten_material_glow" },
    "fill": { "color": "#64748B", "opacity": 0.2, "type": "ambient" }
  },
  "narrationSegments": ["part3_mold_has_three_parts_012"]
}
```

---
