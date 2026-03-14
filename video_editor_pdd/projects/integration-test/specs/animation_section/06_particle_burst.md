[Remotion]

# Section 1.6: Particle Burst

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:07 - 0:08

## Visual Description
A burst of 40 colorful particles explodes outward from the center of the screen. A brief white flash overlay fires at the moment of detonation. Particles radiate outward in all directions with slight angular jitter, decelerating as they travel. Each particle has a randomized color from a blue-indigo-violet-white palette, randomized size, and randomized travel distance. All particles fade to invisible by the end of the animation.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark slate (#1E293B), solid fill
- Origin point: Center (960, 540)

### Chart/Visual Elements
- **Flash overlay:** Full-screen white (#FFFFFF) overlay, peak opacity 0.15, fires on detonation frame
- **Particles:** 40 circles, evenly distributed radially with +/-5 degree jitter per particle
  - Radius range: 4-8px (randomized per particle)
  - Travel distance range: 150-500px from center (randomized per particle)
  - Color palette: #3B82F6 (blue), #6366F1 (indigo), #8B5CF6 (violet), #FFFFFF (white) — randomly assigned
  - Deterministic layout via seeded PRNG (seed: 42, mulberry32 algorithm)

### Animation Sequence
1. **Frame 0-2 (0-0.07s):** Flash — white overlay ramps up to 0.15 opacity then fades back to 0
2. **Frame 2-24 (0.07-0.8s):** Particle travel — all 40 particles radiate outward from center, decelerating; opacity fades from 1 → 0
3. **Frame 24-30 (0.8-1.0s):** Fade out — any remaining particles fully transparent, screen settles to background

### Typography
- None

### Easing
- Flash opacity: `easeOutQuad` (ramp up), `easeInQuad` (fade)
- Particle travel: `easeOutCubic` (deceleration)
- Particle opacity: `linear` fade to 0

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{ backgroundColor: '#1E293B' }}>
  <FlashOverlay />
  {particles.map((p) => (
    <Particle key={p.id} particle={p} />
  ))}
</AbsoluteFill>
```

## Data Points
```json
{
  "particles": {
    "count": 40,
    "minRadius": 4,
    "maxRadius": 8,
    "minDistance": 150,
    "maxDistance": 500,
    "angleJitter": 5,
    "seed": 42
  },
  "flash": {
    "peakOpacity": 0.15
  },
  "colorPalette": ["#3B82F6", "#6366F1", "#8B5CF6", "#FFFFFF"]
}
```

---
