[Remotion]

# Section 1.3: Circle to Square Morph

**Tool:** Remotion
**Duration:** ~1.2s (36 frames @ 30fps)
**Timestamp:** 0:02 - 0:03

## Visual Description
A blue circle (continuing from the previous pulse animation) holds briefly, then smoothly morphs into an indigo rounded square. The transformation interpolates border-radius, size, and color simultaneously. Ghost trails — semi-transparent echoes of the shape at prior states — lag behind the main shape by 3 frames each, creating a motion-blur afterimage effect. Three ghost layers fade from 60% to 15% opacity, adding depth and kinetic energy to the morph.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient from center `#0F172A` to edge `#020617`
- Grid lines: None

### Chart/Visual Elements
- **Start Shape:** Circle — 120px size, border-radius 60px, fill `#3B82F6`, centered at (960, 540)
- **End Shape:** Rounded square — 130px size, border-radius 12px, fill `#6366F1`, centered at (960, 540)
- **Ghost Trail 1:** Opacity 0.60, lags 3 frames behind main shape
- **Ghost Trail 2:** Opacity 0.35, lags 6 frames behind main shape
- **Ghost Trail 3:** Opacity 0.15, lags 9 frames behind main shape
- **Morph Glow:** Soft halo around the shape during transition

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Hold as circle — shape stays at start state (120px, border-radius 60, blue)
2. **Frame 6-30 (0.2-1.0s):** Morph transition — border-radius 60→12px, size 120→130px, color `#3B82F6`→`#6366F1`. Ghost trails follow with 3-frame lag each
3. **Frame 30-36 (1.0-1.2s):** Settle — main shape at final state, ghost trails fade out to 0 opacity

### Typography
- None

### Easing
- Morph (border-radius, size, color): `easeInOut(cubic)`
- Ghost trail fade-out: `easeOut(quad)`

## Narration Sync
> "This is the first section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={36}>
  <MorphGlow center={[960, 540]} />
  {[0.15, 0.35, 0.6].map((opacity, i) => (
    <GhostTrail
      key={i}
      lagFrames={(3 - i) * 3}
      opacity={opacity}
    />
  ))}
  <MorphShape
    startSize={120}
    endSize={130}
    startRadius={60}
    endRadius={12}
    startColor="#3B82F6"
    endColor="#6366F1"
  />
</Sequence>
```

## Data Points
```json
{
  "center": [960, 540],
  "startShape": {
    "size": 120,
    "borderRadius": 60,
    "color": "#3B82F6"
  },
  "endShape": {
    "size": 130,
    "borderRadius": 12,
    "color": "#6366F1"
  },
  "ghostTrails": {
    "opacities": [0.6, 0.35, 0.15],
    "lagFrames": 3
  }
}
```

---
