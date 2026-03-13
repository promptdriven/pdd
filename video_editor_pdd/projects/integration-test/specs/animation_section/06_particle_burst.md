[Remotion]

# Section 1.6: Particle Burst Transition

**Tool:** Remotion
**Duration:** ~0.75s (22 frames @ 30fps)
**Timestamp:** 0:06 – 0:07

## Visual Description
An explosive particle burst erupts from the center of the canvas. A brief white flash signals the burst. Forty particles — half blue circles and half green squares — radiate outward in random directions at varying speeds. Each particle rotates as it travels and fades out over distance. The background color transitions smoothly from charcoal to dark navy, signaling a scene change. The effect is energetic and celebratory, bridging the demonstration beats into the outro.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Transitions from #141921 (charcoal) → #0B1120 (dark navy)
- No grid lines

### Chart/Visual Elements
- **Center flash:** White circle, 30px diameter, 0.8 peak opacity, centered at (640, 360)
- **Blue particles (20x):** Circles, random diameter 6–12px each, #3B82F6
- **Green particles (20x):** Squares, random size 6–10px each, #22C55E, border-radius 1px
- **Particle distribution:** Random angles 0–360°, random speed 200–600 px/sec
- **Particle rotation:** Each particle has random rotation speed -8° to +8° per frame

### Animation Sequence
1. **Frame 0–2 (0–0.07s):** Center flash appears — white circle scales from 0→30px diameter at 0.8 opacity. Instantaneous flash feel.
2. **Frame 2–3 (0.07–0.1s):** Flash fades to 0 opacity. All 40 particles begin outward travel from center (640, 360).
3. **Frame 3–16 (0.1–0.53s):** Particles travel outward along their random trajectories. Each particle:
   - Moves along its angle vector at its assigned speed
   - Rotates continuously at its assigned rotation speed
   - Starts fading from frame 5 onward (opacity 1.0 → 0)
4. **Frame 10–18 (0.33–0.6s):** Background color transitions from #141921 → #0B1120 via linear interpolation.
5. **Frame 16–22 (0.53–0.73s):** All remaining particles fully faded. Canvas rests on #0B1120 background.

### Typography
- None

### Easing
- Flash scale: `easeOutQuad`
- Flash fade: `easeInQuad`
- Particle travel: `linear` (constant velocity, physics-based)
- Particle fade: `easeInCubic` (accelerating fade)
- Particle rotation: `linear` (constant angular velocity)
- Background transition: `easeInOutQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={22}>
  <AbsoluteFill style={{ backgroundColor: bgColor }}>
    {/* Center flash */}
    <Sequence from={0} durationInFrames={3}>
      <CenterFlash diameter={30} opacity={flashOpacity} />
    </Sequence>
    {/* Particles */}
    {particles.map((p, i) => (
      <Particle
        key={i}
        shape={p.shape}
        size={p.size}
        color={p.color}
        angle={p.angle}
        speed={p.speed}
        rotationSpeed={p.rotationSpeed}
        startFrame={2}
        opacity={p.opacity}
      />
    ))}
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "particles": {
    "total": 40,
    "blue": {
      "count": 20,
      "shape": "circle",
      "sizeRange": [6, 12],
      "color": "#3B82F6"
    },
    "green": {
      "count": 20,
      "shape": "square",
      "sizeRange": [6, 10],
      "color": "#22C55E"
    },
    "speedRange": [200, 600],
    "rotationSpeedRange": [-8, 8],
    "fadeStartFrame": 5
  },
  "flash": {
    "diameter": 30,
    "color": "#FFFFFF",
    "peakOpacity": 0.8
  },
  "backgroundTransition": {
    "from": "#141921",
    "to": "#0B1120",
    "startFrame": 10,
    "endFrame": 18
  }
}
```

---
