[Remotion]

# Section 1.3: Circle to Square Morph

**Tool:** Remotion
**Duration:** ~1.1s (33 frames @ 30fps)
**Timestamp:** 0:03 – 0:04

## Visual Description
The blue circle from the previous beat smoothly morphs into a green square. The transformation involves simultaneous changes: border-radius decreases from 50% to 8px, the fill color shifts from blue (#3B82F6) to green (#22C55E), the shape rotates 90 degrees, and the size adjusts from 180px circle to 160px square. A brief morph glow flares during the transition. The square settles with a slight scale overshoot.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark charcoal (#141921)
- No grid lines

### Chart/Visual Elements
- **Starting shape:** Blue circle, 180px diameter, #3B82F6, border-radius 50%, centered
- **Ending shape:** Green square, 160x160px, #22C55E, border-radius 8px, centered
- **Morph glow:** White-tinted aura, 0.25 peak opacity, 250px spread, appears during transformation
- **Drop shadow:** Transitions from blue glow to green glow

### Animation Sequence
1. **Frame 0–5 (0–0.17s):** Hold as blue circle with subtle breathing (1.0x–1.02x scale). No morph yet — continuity from previous beat.
2. **Frame 5–25 (0.17–0.83s):** Morph phase:
   - `border-radius`: 50% → 8px
   - `background-color`: #3B82F6 → #22C55E (color interpolation through HSL)
   - `rotation`: 0° → 90°
   - `size`: 180px → 160px
   - Morph glow rises from 0 → 0.25 opacity (frame 5–15), then fades 0.25 → 0 (frame 15–25)
3. **Frame 25–33 (0.83–1.1s):** Settle — square overshoots to 1.05x scale, then springs back to 1.0x. Drop shadow is now green-tinted: rgba(34, 197, 94, 0.3).

### Typography
- None

### Easing
- Border-radius morph: `easeInOutCubic`
- Color shift: `linear` (through HSL interpolation)
- Rotation: `easeInOutQuad`
- Scale overshoot: `spring({ damping: 14, stiffness: 200, mass: 1 })`
- Glow flare: `easeOutQuad` (in), `easeInQuad` (out)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={33}>
  <AbsoluteFill style={{ backgroundColor: "#141921" }}>
    <MorphGlow
      opacity={morphGlowOpacity}
      spread={250}
    />
    <MorphShape
      borderRadius={interpolate(frame, [5, 25], [90, 8], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
      color={interpolateColors(frame, [5, 25], ["#3B82F6", "#22C55E"])}
      rotation={interpolate(frame, [5, 25], [0, 90], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
      size={interpolate(frame, [5, 25], [180, 160], { extrapolateLeft: "clamp", extrapolateRight: "clamp" })}
      scale={settleScale}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "from": {
    "shape": "circle",
    "size": 180,
    "color": "#3B82F6",
    "borderRadius": "50%"
  },
  "to": {
    "shape": "square",
    "size": 160,
    "color": "#22C55E",
    "borderRadius": 8
  },
  "morph": {
    "rotation": 90,
    "glowOpacity": 0.25,
    "overshootScale": 1.05
  }
}
```

---
