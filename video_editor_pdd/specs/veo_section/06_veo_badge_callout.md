[Remotion]

# Section 2.6: Veo Badge Callout

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:15 - 0:18

## Visual Description
A floating badge appears in the upper-right corner identifying the footage as Veo-generated. The badge is a compact rounded pill with the text "Powered by Veo" and a small sparkle icon. It slides in from the right edge and hovers with a gentle breathing animation (scale pulse), providing attribution without obscuring the footage underneath.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Transparent overlay on top of Veo footage layer

### Chart/Visual Elements
- Badge pill: Rounded rectangle (borderRadius 24px), positioned at top-right (X=1680, Y=60), 200px x 44px
  - Background: rgba(0, 0, 0, 0.7) with backdrop-blur(8px)
  - Border: 1px solid rgba(245, 158, 11, 0.4)
- Sparkle icon: 16x16px SVG, #F59E0B, positioned left of text inside pill
- Badge text: "Powered by Veo"
- Subtle drop shadow: 0 2px 8px rgba(0, 0, 0, 0.3)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Badge slides in from X=1960 (offscreen right) to X=1680. Opacity 0% to 100%.
2. **Frame 15-20 (0.5-0.67s):** Sparkle icon rotates 360 degrees once.
3. **Frame 20-75 (0.67-2.5s):** Badge holds position. Gentle scale breathing: 1.0 → 1.03 → 1.0 over 60 frames, looping.
4. **Frame 75-90 (2.5-3s):** Badge slides out to X=1960. Opacity fades to 0%.

### Typography
- Badge text: Inter SemiBold, 14px, #F59E0B, letter-spacing 0.5px
- No additional labels

### Easing
- Slide in: `easeOutBack` (slight overshoot)
- Sparkle rotation: `easeInOutSine`
- Scale breathing: `easeInOutSine`
- Slide out: `easeInCubic`

## Narration Sync
> (No narration — badge appears as ambient overlay during footage)

## Code Structure (Remotion)
```typescript
<Sequence from={450} durationInFrames={90}>
  <VeoBadge
    text="Powered by Veo"
    icon="sparkle"
    position={{ x: 1680, y: 60 }}
    accentColor="#F59E0B"
  />
</Sequence>
```

## Data Points
```json
{
  "badgeText": "Powered by Veo",
  "accentColor": "#F59E0B",
  "position": { "x": 1680, "y": 60 }
}
```

---
