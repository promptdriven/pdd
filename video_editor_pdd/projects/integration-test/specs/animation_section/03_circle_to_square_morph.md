[Remotion]

# Section 1.3: Circle to Square Morph

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:07 - 0:10

## Visual Description
The blue circle from the previous scene smoothly morphs into a green square. The border-radius animates from 50% (circle) to 0% (square) while the fill color transitions from blue to green. During the morph, the shape rotates 90 degrees, adding visual dynamism to the transformation.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Charcoal (#141921)
- Grid lines: none

### Chart/Visual Elements
- Starting shape: 180px circle, solid fill #3B82F6 (blue), border-radius 50%, centered at (640, 360)
- Ending shape: 160px square, solid fill #22C55E (Tailwind green-500), border-radius 0%, centered at (640, 360)
- Morph glow: Blended color glow transitioning from blue (#3B82F6) to green (#22C55E), 25% opacity, 25px blur

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Shape holds as blue circle (carries over from previous visual). Subtle breathing scale 1.0 → 1.02.
2. **Frame 15-60 (0.5-2.0s):** Border-radius interpolates from 50% → 0%. Fill color interpolates #3B82F6 → #22C55E. Shape rotates from 0° → 90°. Size transitions from 180px diameter to 160px square. Glow color blends in sync.
3. **Frame 60-90 (2.0-3.0s):** Green square settles at center. Brief scale overshoot (1.05 → 1.0). Glow stabilizes as green at 20% opacity.

### Typography
- None (pure shape animation)

### Easing
- Border-radius morph: `easeInOutCubic`
- Color interpolation: `linear` (perceptual color space)
- Rotation: `easeInOutQuad`
- Scale settle: `spring({ damping: 14, stiffness: 200 })`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#141921', justifyContent: 'center', alignItems: 'center' }}>
    <MorphGlow
      fromColor="#3B82F6"
      toColor="#22C55E"
      morphStart={15}
      morphEnd={60}
    />
    <MorphShape
      fromRadius="50%"
      toRadius="0%"
      fromSize={180}
      toSize={160}
      fromColor="#3B82F6"
      toColor="#22C55E"
      rotationDeg={90}
      morphStart={15}
      morphEnd={60}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "fromShape": "circle",
  "toShape": "square",
  "fromColor": "#3B82F6",
  "toColor": "#22C55E",
  "fromSize": 180,
  "toSize": 160,
  "rotationDegrees": 90,
  "morphDurationFrames": 45
}
```

---
