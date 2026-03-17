[veo:]

# Section 2.3: Injection Molding Process — Mold Opens, Parts Eject

**Tool:** Veo
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 8:40 - 8:48

## Visual Description

A close-up cinematic sequence of an injection molding machine in operation. The shot begins tight on the mold — liquid plastic flows into the cavity through the injection nozzle, filling the defined shape. The mold walls are precise, hard edges defining an exact form. Then the mold opens with a satisfying mechanical motion, revealing a perfect plastic part. The part ejects. Then another cycle begins — close, inject, open, eject — with increasing speed, conveying mass production.

A subtle digital counter overlays in the lower-right corner: 1... 10... 100... 10,000... showing the exponential scaling. The counter uses a clean monospace font with low opacity, not distracting from the footage but reinforcing the "unlimited identical parts" concept.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Industrial interior, close-up
- Grid lines: N/A (live-action footage with minor overlay)

### Chart/Visual Elements

**Camera**
- Framing: Close-up (CU) on mold cavity and ejection mechanism
- Movement: Static with subtle vibration from machinery
- Depth of field: shallow, f/2.8 equivalent — mold sharp, background blurred
- Angle: slightly above, looking into the mold cavity

**Lighting**
- Key light: cool blue-white from machine's work light, `#C0D8E8`
- Accent: warm amber from molten plastic, `#D4A043`
- Fill: ambient industrial
- Specular highlights on the precision steel mold surfaces
- Overall tone: cool industrial, warm plastic accent

**Subject**
- Steel mold halves — polished cavity surfaces catching light
- Liquid plastic: translucent amber flowing into cavity
- Ejected parts: clean, identical, pale plastic
- Ejector pins visible in mold half
- Mold opening/closing mechanism (hydraulic)

**Counter Overlay**
- Position: lower-right corner, 120px from edges
- Font: JetBrains Mono, 24px, `#E2E8F0` at 0.3
- Counts: 1, 10, 100, 1,000, 10,000
- Each number fades in/out quickly, accelerating

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Fade in. Close-up on closed mold. Liquid plastic visible entering through nozzle — warm amber glow.
2. **Frame 30-80 (1.0-2.67s):** Mold opens with smooth hydraulic motion. A perfect plastic part is revealed in the cavity. Specular highlights glint on the steel.
3. **Frame 80-120 (2.67-4.0s):** Ejector pins push the part out. Part falls/slides away. Counter shows "1". Mold closes again.
4. **Frame 120-180 (4.0-6.0s):** Cycle repeats at 2x speed. Parts eject. Counter accelerates: 10... 100... The repetition builds momentum.
5. **Frame 180-240 (6.0-8.0s):** Cycle at 4x speed — just flashes of open/close. Counter: 1,000... 10,000. The point lands. Fade begins at frame 230.

### Typography
- Counter: JetBrains Mono, 24px, `#E2E8F0` at 0.3

### Easing
- Counter number transitions: `easeOut(quad)` over 6 frames
- Fade-in: `easeOut(quad)`, 1s
- Fade-out: `easeIn(quad)`, 0.33s
- Speed ramp: exponential acceleration of cycle replay

### Veo Prompt

```
Close-up of an industrial injection molding machine in operation. Steel mold halves open and close with smooth hydraulic motion. Liquid amber-colored plastic flows into the polished steel cavity through an injection nozzle. The mold opens to reveal a perfect plastic part, which is ejected by pins. The cycle repeats with increasing speed. Shallow depth of field, sharp focus on the mold cavity. Cool blue-white work light mixed with warm amber glow from molten plastic. Specular highlights on polished steel surfaces. Industrial precision, mechanical rhythm. Cinematic, 24fps, cool industrial color grade with warm plastic accent.
```

## Narration Sync

> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."
> "Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically."

Segment: `part2_003`
Timing: 8:40 - 8:48

- **8:40** ("Consider injection molding"): Mold visible, plastic flowing in
- **8:43** ("After it? You designed molds"): Mold opens, first part ejects
- **8:45** ("Make the mold once, produce unlimited"): Cycle accelerates, counter climbing

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={240}>
  <VeoClip
    clipId="injection_molding_process"
    src="/clips/injection_molding_process.mp4"
    fit="cover"
  />

  {/* Counter overlay */}
  <Sequence from={80}>
    <CounterOverlay
      values={[1, 10, 100, 1000, 10000]}
      timings={[0, 40, 60, 75, 85]}
      font="JetBrains Mono" size={24}
      color="#E2E8F0" opacity={0.3}
      position={[1780, 980]} align="right"
    />
  </Sequence>

  {/* Fade in */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn />
  </Sequence>
  {/* Fade out */}
  <Sequence from={230} durationInFrames={10}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points JSON

```json
{
  "type": "veo_clip",
  "clipId": "injection_molding_process",
  "camera": {
    "framing": "close_up",
    "movement": "static_with_vibration",
    "dof": "shallow",
    "angle": "slightly_above"
  },
  "lighting": {
    "key": { "color": "#C0D8E8", "position": "work_light", "type": "cool_industrial" },
    "accent": { "color": "#D4A043", "source": "molten_plastic" },
    "grade": "cool_industrial_warm_accent"
  },
  "overlay": {
    "counter": {
      "values": [1, 10, 100, 1000, 10000],
      "position": "lower_right"
    }
  },
  "narrationSegments": ["part2_003"],
  "narrationTimingSeconds": { "start": 520.0, "end": 528.0 }
}
```

---
