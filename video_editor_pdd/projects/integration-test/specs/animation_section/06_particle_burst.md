[Remotion]

# Section 1.6: Particle Burst

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:05.7 - 0:06.7

## Visual Description
A particle burst effect erupts from the center of the canvas. 40 small circles (4-8px radius) explode outward from a central point in all directions, each following a random radial trajectory. Particles are colored in a palette of blue (#3B82F6), indigo (#6366F1), violet (#8B5CF6), and white (#FFFFFF). Each particle fades from full opacity to 0 as it travels outward. A brief white flash (full-canvas overlay at 15% opacity) precedes the burst. Particles slow down as they spread, simulating deceleration.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Charcoal #1E293B
- Grid lines: None

### Chart/Visual Elements
- Burst origin: center (960, 540)
- Particle count: 40
- Particle radius: randomly 4px to 8px
- Particle colors: randomly assigned from [#3B82F6, #6366F1, #8B5CF6, #FFFFFF]
- Particle travel distance: 150px to 500px from origin (random per particle)
- Particle angles: evenly distributed 0-360 degrees with slight random jitter (+/- 5 degrees)
- Flash overlay: full canvas, white (#FFFFFF) at 15% opacity

### Animation Sequence
1. **Frame 0-2 (0-0.07s):** White flash overlay appears and fades
2. **Frame 2-6 (0.07-0.2s):** Particles spawn at center, begin radiating outward rapidly
3. **Frame 6-24 (0.2-0.8s):** Particles continue outward, decelerating; opacity fades from 1.0 to 0
4. **Frame 24-30 (0.8-1.0s):** Final particles fade out completely; canvas returns to background only

### Typography
- None

### Easing
- Flash: `easeOutExpo`
- Particle radial movement: `easeOutQuart`
- Particle opacity fade: `easeInQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <Sequence from={0} durationInFrames={6}>
    <FlashOverlay color="#FFFFFF" peakOpacity={0.15} />
  </Sequence>
  <Sequence from={2}>
    <ParticleBurst
      count={40}
      origin={[960, 540]}
      colors={["#3B82F6", "#6366F1", "#8B5CF6", "#FFFFFF"]}
      minRadius={4}
      maxRadius={8}
      minDistance={150}
      maxDistance={500}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "burst": {
    "origin": [960, 540],
    "particleCount": 40,
    "colors": ["#3B82F6", "#6366F1", "#8B5CF6", "#FFFFFF"],
    "radiusRange": [4, 8],
    "distanceRange": [150, 500],
    "seed": 42
  }
}
```

---
