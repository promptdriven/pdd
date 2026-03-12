[Remotion]

# Section 1.6: Particle Burst Transition

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:16 - 0:18

## Visual Description
A burst of colored particles explodes outward from the center of the screen, combining blue and green particles that reference the two shapes from the section. The particles radiate in a circular pattern, fade out as they reach the edges, and the screen transitions to the dark background for the closing card.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Charcoal (#141921), transitioning to Dark navy (#0B1120) by end
- Grid lines: none

### Chart/Visual Elements
- Particle system: 40 particles total, spawning from center point (640, 360)
- Blue particles (20): circles, 6-12px diameter, fill #3B82F6, random velocities outward
- Green particles (20): squares, 6-10px, fill #22C55E, random velocities outward
- Each particle has randomized: angle (0-360°), speed (200-600px/s), size, rotation speed
- Flash: White (#FFFFFF) circle, 30px, at center, 80% opacity, visible for 3 frames

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** White center flash appears and fades immediately. All 40 particles spawn at center.
2. **Frame 3-30 (0.1-1.0s):** Particles travel outward along their radial trajectories. Particles rotate individually. Opacity starts at 100% and begins fading after frame 15.
3. **Frame 30-50 (1.0-1.67s):** Particles continue outward, opacity fading to 0%. Particles that reach canvas edge disappear. Background begins transitioning from #141921 to #0B1120.
4. **Frame 50-60 (1.67-2.0s):** All particles gone. Background fully settled at #0B1120. Screen is clear.

### Typography
- None

### Easing
- Particle velocity: `easeOutQuad` (decelerate as they spread)
- Particle opacity fade: `linear`
- Center flash: `easeOutExpo`
- Background transition: `easeInOutSine`

## Narration Sync
> (No narration — transition beat)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill>
    <BackgroundTransition from="#141921" to="#0B1120" start={30} end={50} />
    <CenterFlash duration={3} color="#FFFFFF" size={30} />
    <ParticleSystem
      count={40}
      particles={[
        { type: 'circle', color: '#3B82F6', count: 20 },
        { type: 'square', color: '#22C55E', count: 20 },
      ]}
      origin={{ x: 640, y: 360 }}
      speedRange={[200, 600]}
      sizeRange={[6, 12]}
      fadeStart={15}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "particleCount": 40,
  "groups": [
    { "shape": "circle", "color": "#3B82F6", "count": 20 },
    { "shape": "square", "color": "#22C55E", "count": 20 }
  ],
  "origin": { "x": 640, "y": 360 },
  "speedRange": [200, 600],
  "sizeRange": [6, 12]
}
```

---
