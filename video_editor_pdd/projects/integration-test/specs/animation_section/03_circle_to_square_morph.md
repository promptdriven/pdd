[Remotion]

# Section 1.3: Circle to Square Morph

**Tool:** Remotion
**Duration:** ~1.2s
**Timestamp:** 0:02.5 - 0:03.7

## Visual Description
The blue circle from the previous component smoothly morphs into a rounded square. The shape transitions by interpolating `borderRadius` from 50% (circle) to 12px (rounded rectangle). During the morph, the color shifts from blue (#3B82F6) to indigo (#6366F1). The shape maintains a consistent 120x120px bounding box throughout the transition. A faint motion trail (3 ghost copies at decreasing opacity) follows the shape during the morph.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Charcoal #1E293B with radial gradient to #0F172A at edges
- Grid lines: None

### Chart/Visual Elements
- Shape: centered at (960, 540), 120x120px bounding box
- Start state: circle (borderRadius 50%), fill #3B82F6
- End state: rounded square (borderRadius 12px), fill #6366F1
- Ghost trails: 3 copies at 15%, 10%, 5% opacity, offset 0/4/8 frames behind

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Shape holds as circle, slight scale up from 1.0 to 1.05
2. **Frame 6-30 (0.2-1.0s):** borderRadius interpolates from 50% to 12px; color interpolates from #3B82F6 to #6366F1; ghost trails visible
3. **Frame 30-36 (1.0-1.2s):** Shape settles at final square state, ghost trails fade out, slight scale settle from 1.05 to 1.0

### Typography
- None

### Easing
- Border radius morph: `easeInOutCubic`
- Color interpolation: `linear`
- Scale settle: `easeOutQuad`
- Ghost trail opacity: `linear`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={36}>
  <MorphShape
    fromRadius="50%"
    toRadius={12}
    fromColor="#3B82F6"
    toColor="#6366F1"
    size={120}
  >
    <GhostTrail count={3} opacities={[0.15, 0.1, 0.05]} />
  </MorphShape>
</Sequence>
```

## Data Points
```json
{
  "morph": {
    "fromShape": "circle",
    "toShape": "roundedSquare",
    "fromColor": "#3B82F6",
    "toColor": "#6366F1",
    "size": 120,
    "borderRadiusStart": "50%",
    "borderRadiusEnd": "12px"
  }
}
```

---
