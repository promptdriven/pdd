[Remotion] Monitor Glow Ambient Overlay

# Section 0.7: Monitor Glow Ambient Overlay

**Tool:** Remotion
**Duration:** ~15.68s (full section)
**Timestamp:** 0:00 - 0:15.68

## Visual Description
A subtle animated light overlay that enhances the "code glow" atmosphere across the entire cold open. Soft radial gradients in blue and amber pulse gently at the edges of the frame, simulating the ambient light cast by monitors onto surrounding surfaces. This is a compositing enhancement layer — it adds cinematic depth to the Veo footage without obscuring it. The effect is barely perceptible consciously but creates a richer, more immersive visual environment.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Blend mode: screen (additive light)
- Overall opacity: 15-25% (very subtle)

### Chart/Visual Elements
- Glow A (left edge): radial gradient centered at (-200, 540)
  - Color: #3B82F6 (vibrant blue) → transparent
  - Radius: 600px
  - Opacity: oscillates 15%→25%→15% over 6s cycle
- Glow B (right edge): radial gradient centered at (2120, 400)
  - Color: #60A5FA (cool monitor blue) → transparent
  - Radius: 500px
  - Opacity: oscillates 20%→10%→20% over 8s cycle (counter-phased to Glow A)
- Glow C (top-right accent): radial gradient centered at (1600, -100)
  - Color: #F59E0B (amber accent) → transparent
  - Radius: 400px
  - Opacity: constant 8%
  - Purpose: subtle warm accent to break monochrome blue

### Animation Sequence
1. **Frame 0-470 (0-15.68s):** Continuous gentle pulsing of Glow A and B
2. **Glow A cycle:** sin(frame * 0.035) maps to opacity [0.15, 0.25] — ~6s period
3. **Glow B cycle:** sin(frame * 0.026 + π) maps to opacity [0.10, 0.20] — ~8s period, offset
4. **Glow C:** static, no animation
5. **Respects fade bookends:** entire overlay fades with the black fade-in/out (06_fade_bookends.md controls visibility)

### Typography
- None

### Easing
- Glow pulsing: sinusoidal (no easing — continuous smooth oscillation)

## Narration Sync
> Runs throughout entire cold open narration. No specific sync points.

This is an ambient atmospheric layer with no narration-driven triggers.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={470}>
  <AbsoluteFill style={{ mixBlendMode: 'screen', pointerEvents: 'none' }}>
    {/* Left blue glow */}
    <RadialGlow
      center={[-200, 540]}
      radius={600}
      color="#3B82F6"
      opacity={interpolate(Math.sin(frame * 0.035), [-1, 1], [0.15, 0.25])}
    />
    {/* Right blue glow — counter-phased */}
    <RadialGlow
      center={[2120, 400]}
      radius={500}
      color="#60A5FA"
      opacity={interpolate(Math.sin(frame * 0.026 + Math.PI), [-1, 1], [0.10, 0.20])}
    />
    {/* Top-right amber accent — static */}
    <RadialGlow
      center={[1600, -100]}
      radius={400}
      color="#F59E0B"
      opacity={0.08}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "glows": [
    {
      "id": "glow_a",
      "position": [-200, 540],
      "radius": 600,
      "color": "#3B82F6",
      "opacity_range": [0.15, 0.25],
      "cycle_seconds": 6
    },
    {
      "id": "glow_b",
      "position": [2120, 400],
      "radius": 500,
      "color": "#60A5FA",
      "opacity_range": [0.10, 0.20],
      "cycle_seconds": 8
    },
    {
      "id": "glow_c",
      "position": [1600, -100],
      "radius": 400,
      "color": "#F59E0B",
      "opacity": 0.08,
      "animated": false
    }
  ],
  "blend_mode": "screen",
  "total_frames": 470
}
```

---
