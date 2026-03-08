[Remotion]

# Section 1.3: Particle Burst Transition

**Tool:** Remotion
**Duration:** ~1.5s (45 frames)
**Timestamp:** 0:02 - 0:04

## Visual Description
A rapid transition beat between the title card and the key visual. The 60 floating particles from the title card accelerate outward in a radial burst from the screen center, leaving trails that fade to black. The background gradient cross-fades from the navy-blue palette (#0A1628/#1E3A8A) to solid red (#FF0000), bridging the two visual styles.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Cross-fade from `linear-gradient(180deg, #0A1628, #1E3A8A)` to solid `#FF0000`
- No grid lines

### Chart/Visual Elements
- **Particle burst:** 60 circles (2-6px diameter), color #3B82F6, exploding radially from center point (960, 540)
- **Particle trails:** Each particle leaves a fading tail (3 ghost copies at 60%, 30%, 10% opacity) behind its motion vector
- **Background gradient morph:** Smooth transition between two background states
- **Vignette overlay:** Radial gradient from transparent center to rgba(0,0,0,0.4) edges, intensifies during burst

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Particles gather toward center (960, 540), shrinking from original positions
2. **Frame 10-15 (0.33-0.5s):** Brief hold — particles cluster tightly at center, flash pulse (white circle 20px, opacity 0→1→0)
3. **Frame 15-35 (0.5-1.17s):** Radial explosion — particles fly outward at randomized velocities (speed 8-15px/frame), trailing ghost copies
4. **Frame 15-35 (0.5-1.17s):** Background cross-fades from gradient to solid red simultaneously
5. **Frame 35-45 (1.17-1.5s):** Particles exit frame edges, trails fade to 0 opacity, red background settles

### Typography
- None (transition-only visual)

### Easing
- Particle gather: `easeInQuad` (accelerating inward)
- Flash pulse: `easeOutExpo` (sharp peak, fast decay)
- Radial explosion: `easeOutCubic` (fast start, decelerating)
- Background cross-fade: `easeInOutSine` (smooth blend)

## Narration Sync
> "This is the first section of the integration test video."

This transition overlaps the tail of segment 1 (~2.0s-3.0s) and bridges into segment 2. The burst punctuates the end of the introductory narration.

## Code Structure (Remotion)
```typescript
<Sequence from={58} durationInFrames={45}>
  <AbsoluteFill>
    {/* Cross-fading background */}
    <BackgroundMorph
      from={{ gradient: ['#0A1628', '#1E3A8A'] }}
      to={{ solid: '#FF0000' }}
      startFrame={15}
      endFrame={35}
    />
    {/* Vignette */}
    <RadialVignette intensity={0.4} />
    {/* Particle burst system */}
    <ParticleBurst
      count={60}
      centerX={960}
      centerY={540}
      gatherFrames={[0, 10]}
      burstFrame={15}
      particleColor="#3B82F6"
      trailCopies={3}
    />
    {/* Center flash */}
    <Sequence from={10} durationInFrames={10}>
      <CenterFlash color="#FFFFFF" maxRadius={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "particleCount": 60,
  "burstCenter": { "x": 960, "y": 540 },
  "burstVelocityRange": [8, 15],
  "trailGhostCopies": 3,
  "trailOpacities": [0.6, 0.3, 0.1],
  "backgroundFrom": ["#0A1628", "#1E3A8A"],
  "backgroundTo": "#FF0000"
}
```

---
