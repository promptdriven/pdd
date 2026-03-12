[title:]

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:00 - 0:03

## Visual Description
A full-screen title card introduces the Veo Section. The background is a deep ocean-blue gradient that evokes the calm coastal imagery to follow. The section title fades in at center screen, followed by a thin horizontal rule that draws outward from the center. A subtle particle drift (small soft-focus dots) floats upward across the frame to add depth.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: linear gradient top-to-bottom #0B1D3A → #162D50
- No grid lines

### Chart/Visual Elements
- Title text: "Veo Section" — centered horizontally and vertically
- Horizontal rule: 200px wide, 2px height, color #5B9BD5, centered below title
- Particle layer: 15–20 small circles (r=2–4px), color #FFFFFF at 10–20% opacity, drifting upward at randomized speeds

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background gradient fades in from black
2. **Frame 15-45 (0.5-1.5s):** Title text fades in and shifts up 10px (parallax entrance)
3. **Frame 30-60 (1-2s):** Horizontal rule draws outward from center (scaleX 0→1)
4. **Frame 0-90 (0-3s):** Particle drift runs continuously across full duration

### Typography
- Title: Inter Bold, 64px, #FFFFFF
- No additional labels

### Easing
- Title fade-in: `easeOutCubic`
- Rule draw: `easeInOutQuad`
- Particle drift: `linear`

## Narration Sync
> (No narration — pre-roll title card before first narrator line)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <GradientBackground colors={["#0B1D3A", "#162D50"]} />
  <Sequence from={15}>
    <FadeIn>
      <TitleText text="Veo Section" font="Inter" size={64} color="#FFFFFF" />
    </FadeIn>
  </Sequence>
  <Sequence from={30}>
    <HorizontalRule width={200} color="#5B9BD5" />
  </Sequence>
  <ParticleDrift count={18} color="#FFFFFF" opacity={0.15} />
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Section",
  "background_colors": ["#0B1D3A", "#162D50"]
}
```

---
