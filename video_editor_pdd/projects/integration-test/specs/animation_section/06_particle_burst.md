[Remotion]

# Section 1.6: Particle Burst

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:05 - 0:06

## Visual Description
A dramatic particle explosion erupts from the center of the screen. A bright white flash expands and contracts rapidly, then 40 particles shoot outward in all directions from the origin point. Particles vary in size (3-8px radius) and travel at different speeds, colored in a palette of blue, indigo, purple, and light gray. Each particle fades out as it reaches the edge of its travel distance, creating a firework-like burst effect against a near-black background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Near-black `#020617` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Central Flash:** White `#FFFFFF` circle
  - Max radius: 120px (expanding phase)
  - Contracted radius: 60px
  - Peak opacity: 0.8
- **Particles:** 40 total, seeded random (seed=42)
  - Colors: `#3B82F6` (blue), `#6366F1` (indigo), `#8B5CF6` (purple), `#E2E8F0` (light gray)
  - Radius range: 3-8px per particle
  - Speed range: 200-600 px/s
  - Max travel distance: 300px from origin
  - Origin: (960, 540)
  - Fade start: at 60% of travel distance

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** Flash expand — white circle grows from 0→120px radius, opacity rises to 0.8
2. **Frame 3-6 (0.1-0.2s):** Flash contract/fade — radius 120→60px, opacity 0.8→0
3. **Frame 3-22 (0.1-0.73s):** Particles radiate outward from center, each traveling at its own speed/direction. Particles begin fading after reaching 60% of max distance
4. **Frame 22-30 (0.73-1.0s):** Particle tail fade — remaining particles fade to 0 opacity

### Typography
- None

### Easing
- Flash expand: `easeOut(quad)`
- Flash contract: `easeIn(quad)`
- Particle movement: `easeOut(cubic)`
- Particle fade: `easeIn(quad)`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <FlashOverlay
    center={[960, 540]}
    maxRadius={120}
    contractedRadius={60}
    peakOpacity={0.8}
  />
  {particles.map((p, i) => (
    <Particle
      key={i}
      origin={[960, 540]}
      angle={p.angle}
      speed={p.speed}
      radius={p.radius}
      color={p.color}
      maxDistance={300}
      fadeStartRatio={0.6}
    />
  ))}
</Sequence>
```

## Data Points
```json
{
  "origin": [960, 540],
  "particleCount": 40,
  "seed": 42,
  "colors": ["#3B82F6", "#6366F1", "#8B5CF6", "#E2E8F0"],
  "radiusRange": [3, 8],
  "speedRange": [200, 600],
  "maxDistance": 300,
  "fadeStartRatio": 0.6,
  "flash": {
    "maxRadius": 120,
    "contractedRadius": 60,
    "peakOpacity": 0.8,
    "color": "#FFFFFF"
  }
}
```

---
