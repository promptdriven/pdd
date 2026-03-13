[Remotion]

# Section 1.2: Blue Circle Pulse

**Tool:** Remotion
**Duration:** ~1.5s (45 frames @ 30fps)
**Timestamp:** 0:01 – 0:03

## Visual Description
A single blue circle appears at the center of a dark charcoal canvas, scaling in with a spring-based overshoot animation. Once settled, a soft blue glow ring fades in around the circle. The circle then executes a single pronounced pulse beat — scaling up to 1.15x before settling back. The glow ring oscillates gently for the remainder of the beat, creating a breathing, alive quality.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark charcoal (#141921)
- No grid lines

### Chart/Visual Elements
- **Blue circle:** 180px diameter, #3B82F6 (Tailwind blue-500), centered on canvas (640, 360)
- **Drop shadow:** 0px 0px 40px rgba(59, 130, 246, 0.3), applied to circle
- **Glow ring:** 220–280px diameter annulus around circle, #3B82F6 at 15% opacity, 30px gaussian blur

### Animation Sequence
1. **Frame 0–8 (0–0.27s):** Circle scales from 0→1.08x (spring overshoot). Uses spring config: damping 12, stiffness 180, mass 1.
2. **Frame 8–15 (0.27–0.5s):** Circle settles from 1.08x→1.0x. Glow ring fades in from 0→0.15 opacity. Drop shadow intensifies from 0→full.
3. **Frame 15–28 (0.5–0.93s):** Pulse beat — circle scales smoothly from 1.0x→1.15x→1.0x over 13 frames. Glow ring expands from 220px→280px and back.
4. **Frame 28–45 (0.93–1.5s):** Rest phase — gentle breathing oscillation at 1.0x–1.02x scale on a 15-frame sinusoidal cycle. Glow pulses 0.12–0.18 opacity.

### Typography
- None

### Easing
- Scale-in: `spring({ damping: 12, stiffness: 180, mass: 1 })`
- Pulse beat: `easeInOutCubic`
- Breathing: `sinusoidal` (continuous)
- Glow fade: `easeOutQuad`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={45}>
  <AbsoluteFill style={{ backgroundColor: "#141921" }}>
    <GlowRing
      diameter={glowDiameter}
      color="#3B82F6"
      opacity={glowOpacity}
      blur={30}
    />
    <PulsingCircle
      diameter={180}
      color="#3B82F6"
      scale={circleScale}
      shadow="0px 0px 40px rgba(59, 130, 246, 0.3)"
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "circle": {
    "diameter": 180,
    "color": "#3B82F6",
    "position": [640, 360]
  },
  "glow": {
    "minDiameter": 220,
    "maxDiameter": 280,
    "blur": 30,
    "opacity": 0.15
  },
  "spring": {
    "damping": 12,
    "stiffness": 180,
    "mass": 1
  },
  "pulseScale": 1.15,
  "breathingScale": 1.02
}
```

---
