[Remotion]

# Section 1.3: Circle to Square Morph

**Tool:** Remotion
**Duration:** ~1.2s (36 frames @ 30fps)
**Timestamp:** 0:04 - 0:05

## Visual Description
The blue circle from the previous visual smoothly morphs into a rounded square. The border-radius transitions from fully circular to a subtle 12px rounding, while the fill color shifts from blue to indigo. Ghost trail echoes of the shape at previous frames lag behind the morph, creating a motion-blur effect, then fade out as the shape settles.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient — dark slate (#1E293B) at center to dark navy (#0F172A) at edges

### Chart/Visual Elements
- **Morphing shape:** Centered at (960, 540), 120x120px
  - Start state: border-radius 60px (circle), fill #3B82F6 (blue)
  - End state: border-radius 12px (rounded square), fill #6366F1 (indigo)
- **Ghost trail:** 3 semi-transparent echoes lagging behind the morph
  - Ghost 1: opacity 0.15, 0-frame offset
  - Ghost 2: opacity 0.10, 4-frame offset
  - Ghost 3: opacity 0.05, 8-frame offset

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Hold as circle — shape remains at border-radius 60px, blue fill
2. **Frame 6-30 (0.2-1.0s):** Morph — border-radius interpolates 60px → 12px, color interpolates #3B82F6 → #6366F1, ghost trails visible
3. **Frame 30-36 (1.0-1.2s):** Settle — shape at final state, ghost trails fade out

### Typography
- None

### Easing
- Border-radius morph: `easeInOutCubic`
- Color transition: `linear`
- Ghost trail opacity: `easeOut`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{
  background: 'radial-gradient(circle at 50% 50%, #1E293B 0%, #0F172A 100%)'
}}>
  <GhostTrail />
  <MorphShape />
</AbsoluteFill>
```

## Data Points
```json
{
  "shape": {
    "size": 120,
    "borderRadiusStart": 60,
    "borderRadiusEnd": 12,
    "colorStart": "#3B82F6",
    "colorEnd": "#6366F1"
  },
  "ghostTrail": {
    "count": 3,
    "opacities": [0.15, 0.10, 0.05],
    "frameOffsets": [0, 4, 8]
  }
}
```

---
