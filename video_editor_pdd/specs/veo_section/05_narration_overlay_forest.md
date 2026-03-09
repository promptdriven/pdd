[Remotion]

# Section 2.5: Narration Overlay — Forest

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:12 - 0:15

## Visual Description
A narration text overlay appears over the continuing aerial forest footage. The text "It uses Veo-generated clips with narration overlay." fades in within the same frosted-glass pill style established in the intro overlay, maintaining visual consistency. The progress bar tracks narration timing in a green accent to complement the forest visuals.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Transparent overlay on top of Veo footage layer

### Chart/Visual Elements
- Frosted-glass pill: Rounded rectangle (borderRadius 16px), centered horizontally at Y=780, width auto-fit to text + 48px padding, height 64px
  - Background: rgba(0, 0, 0, 0.55) with backdrop-blur(12px)
  - Border: 1px solid rgba(255, 255, 255, 0.1)
- Narration text: Centered inside pill
- Progress bar: 3px tall, bottom edge of pill, fills left-to-right
  - Color: #34D399 (emerald accent, complementing forest visuals)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Pill container fades in from 0% to 100% opacity, slides up from Y=800 to Y=780.
2. **Frame 10-20 (0.33-0.67s):** Narration text fades in from 0% to 100% opacity.
3. **Frame 15-75 (0.5-2.5s):** Progress bar fills from 0% to 100% width.
4. **Frame 75-90 (2.5-3s):** Entire pill and text fade out to 0% opacity.

### Typography
- Narration text: Inter Medium, 28px, #FFFFFF, text-align center
- No additional labels

### Easing
- Pill fade/slide: `easeOutCubic`
- Text fade: `easeOutQuad`
- Progress bar: `linear`
- Fade out: `easeInQuad`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={360} durationInFrames={90}>
  <NarrationPill
    text="It uses Veo-generated clips with narration overlay."
    progressColor="#34D399"
    position={{ x: "center", y: 780 }}
  />
</Sequence>
```

## Data Points
```json
{
  "narrationText": "It uses Veo-generated clips with narration overlay.",
  "pillBackground": "rgba(0, 0, 0, 0.55)",
  "progressColor": "#34D399"
}
```

---
