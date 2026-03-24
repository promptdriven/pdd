[veo:]

# Section 2.3: Factory Floor Intro — Industrial Injection Molding

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:49 - 0:57

## Visual Description

A cinematic establishing shot of an industrial factory floor. An injection molding machine dominates the frame — massive, mechanical, imposing. The lighting is industrial: overhead fluorescents with warm tungsten accents from machinery indicator lights. Steam or mist drifts across the background. The mood is purposeful, powerful — this is where things are *made*.

The camera starts wide to establish scale, then drifts subtly toward the injection molding machine. The factory is clean and operational — not abandoned or dystopian. Workers may be visible in the background, but the machine is the star.

This clip establishes the manufacturing metaphor that runs through the entire section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Industrial factory interior
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Wide establishing shot, then slow drift toward the injection molding machine
- Movement: Subtle dolly forward, 2-3 feet over 8 seconds
- Depth of field: Deep, f/5.6 — most of the factory floor in focus
- Angle: Eye-level to slightly low, emphasizing the scale of the machine

**Lighting**
- Key light: Overhead industrial fluorescents `#F0F0EC` — diffused, even
- Fill: Warm tungsten from machinery indicators `#FFB347` at 0.2
- Accent: Subtle blue from status LEDs on machine panel `#4A90D9` at 0.1
- Atmosphere: Light haze or steam in background for depth

**Subject**
- Injection molding machine: Large industrial unit, metal and hydraulic
- Factory floor: Clean concrete, organized. Pallets of parts visible in background.
- No close-up on specific details — this is the establishing shot.

### Animation Sequence
1. **Frame 0-120 (0-4s):** Wide establishing shot. Factory floor with injection molding machine. Camera slowly drifts forward.
2. **Frame 120-240 (4-8s):** Continue forward drift. The machine fills more of the frame. Industrial sounds implied.

### Typography
- None (pure B-roll footage)

### Easing
- Camera drift: natural, steady dolly-in
- Hard cut in and out

### Veo Prompt

```
Wide establishing shot of a modern industrial factory floor. A large injection molding machine dominates the center of the frame, made of steel and hydraulic components. Clean concrete floor, organized factory environment. Overhead fluorescent lighting with warm tungsten accents from machinery indicator lights. Light haze or steam drifts through the background, adding atmospheric depth. Camera slowly drifts forward toward the machine over 8 seconds. Deep focus, cinematic, 24fps. The mood is industrial, purposeful, and powerful — a place where precision manufacturing happens at scale.
```

## Narration Sync
> "Well, there's a pattern here that shows up across industries. Not just cheaper materials — a deeper shift in how things are made."
> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."

Segments: `part2_paradigm_shift_005`, `part2_paradigm_shift_006`

- **0:49** ("pattern here that shows up"): Factory floor establishing shot appears
- **0:54** ("injection molding"): Camera has drifted closer to the machine

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="factory_floor_intro"
    src="/clips/factory_floor_intro.mp4"
    fit="cover"
  />
</Sequence>
```

## Data Points JSON
```json
{
  "type": "veo_clip",
  "clipId": "factory_floor_intro",
  "camera": {
    "framing": "wide_establishing",
    "movement": "slow_dolly_forward",
    "dof": "deep",
    "aperture": "f/5.6",
    "angle": "eye_level_to_low"
  },
  "lighting": {
    "key": { "color": "#F0F0EC", "type": "overhead_fluorescent" },
    "fill": { "color": "#FFB347", "opacity": 0.2, "type": "machinery_indicators" },
    "accent": { "color": "#4A90D9", "opacity": 0.1, "type": "status_leds" },
    "atmosphere": "light_haze"
  },
  "narrationSegments": ["part2_paradigm_shift_005", "part2_paradigm_shift_006"]
}
```

---
