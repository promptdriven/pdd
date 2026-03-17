[veo:]

# Section 2.2: Factory Floor Intro — Industrial Setting

**Tool:** Veo
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 8:34 - 8:40

## Visual Description

A cinematic establishing shot of an industrial factory floor. The camera glides forward through a clean, modern plastics manufacturing facility. An injection molding machine dominates the frame — large, steel, imposing. Warm overhead industrial lighting catches metal surfaces. The floor is polished concrete. The atmosphere is purposeful and precise — this is serious engineering, not artisanal craft.

The camera movement is a slow dolly forward, creating a sense of approach and discovery. Steam or condensation wisps drift past, catching the light. The shot establishes the manufacturing context before diving into the injection molding metaphor.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Industrial interior, mixed lighting
- Grid lines: N/A (live-action footage)

### Chart/Visual Elements

**Camera**
- Framing: Wide establishing shot, transitioning to medium shot of the machine
- Movement: Slow dolly forward, ~8% travel over 6 seconds
- Depth of field: moderate, f/4.0 equivalent — foreground sharp, background slightly soft
- Angle: slightly low, looking up at the machine (conveys scale)

**Lighting**
- Key light: warm industrial overhead, `#E8C87A`, diffused
- Practicals: machinery indicator lights, green/amber dots
- Fill: ambient bounce off polished concrete floor
- Overall tone: industrial warm, shadows pushed toward `#1A1612`
- Steam/condensation catching light from upper right

**Subject**
- Central: large injection molding machine, steel and dark blue painted surfaces
- Hopper visible at top (where pellets enter)
- Hydraulic press mechanism visible
- Floor: polished concrete, slight sheen
- Background: additional machines in soft focus, creating depth

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Shot fades in. Wide view of factory floor. Steam wisps drift. Industrial ambiance.
2. **Frame 30-90 (1.0-3.0s):** Camera dollies forward. The injection molding machine grows in frame. Details become visible — control panel, hydraulic arms, hopper.
3. **Frame 90-140 (3.0-4.67s):** Camera reaches medium shot. Machine fills 60% of frame. Indicator lights glow. The precision of the equipment is evident.
4. **Frame 140-180 (4.67-6.0s):** Hold on the machine. A subtle mechanical movement — the press cycling. Fade begins at frame 170.

### Typography
- None (pure B-roll footage)

### Easing
- Camera dolly: `linear` (smooth mechanical tracking)
- Fade-in: `easeOut(quad)`, 1s
- Fade-out: `easeIn(quad)`, 0.33s

### Veo Prompt

```
Slow dolly forward through a modern plastics manufacturing factory floor. A large industrial injection molding machine dominates the center of frame, steel and dark blue painted surfaces, hydraulic press mechanism visible. Warm overhead industrial lighting, polished concrete floor with slight sheen. Wisps of steam or condensation drift through the light from upper right. Slightly low camera angle looking up at the machine to convey scale. Clean, organized facility. Industrial, purposeful atmosphere. Cinematic, 24fps, warm industrial color grade, moderate depth of field.
```

## Narration Sync

> "There's a pattern here that shows up across industries. Not just cheaper materials — a deeper shift in how things are made."

Segment: `part2_002`
Timing: 8:34 - 8:40 (continues from title card)

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={180}>
  <VeoClip
    clipId="factory_floor_intro"
    src="/clips/factory_floor_intro.mp4"
    fit="cover"
  />
  {/* Fade in */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={170} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "factory_floor_intro",
  "camera": {
    "framing": "wide_to_medium",
    "movement": "dolly_forward",
    "travelPercent": 8,
    "dof": "moderate",
    "angle": "slightly_low"
  },
  "lighting": {
    "key": { "color": "#E8C87A", "position": "overhead", "type": "industrial" },
    "fill": "ambient_bounce",
    "grade": "industrial_warm"
  },
  "narrationSegments": ["part2_002"],
  "narrationTimingSeconds": { "start": 514.0, "end": 520.0 }
}
```

---
