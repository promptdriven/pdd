[title:] Veo Section Title Card

# Section 2.1: Veo Section Title Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:07 – 0:10

## Visual Description
A cinematic title card introducing the Veo Section. A deep ocean-blue gradient fills the screen while 18 soft white particles drift upward like dust motes. The section title "Veo Section" fades in at centre with a subtle upward parallax shift, followed by a thin blue horizontal rule that draws outward from the midpoint beneath the text.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Linear gradient from `#0B1D3A` (top) to `#162D50` (bottom)
- Gradient direction: top-to-bottom

### Chart/Visual Elements
- **Title text:** "Veo Section" centred horizontally and vertically
- **Horizontal rule:** 200px wide, 2px tall, colour `#5B9BD5`, positioned 24px below title
- **Particle field:** 18 white circles (radius 2–4px, opacity 0.15) drifting upward at 1.5–4.0 px/frame with 1px blur

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Background gradient fades in from black (opacity 0 → 1)
2. **Frame 15–45 (0.5–1.5s):** Title text fades in (opacity 0 → 1) and slides up 10px → 0px with `easeOutCubic`
3. **Frame 30–60 (1.0–2.0s):** Horizontal rule scales from centre outward (scaleX 0 → 1) with `easeInOutQuad`
4. **Frame 0–90 (0–3.0s):** Particle drift runs continuously; particles wrap from top back to bottom

### Typography
- Title: Inter, 64px, bold, `#FFFFFF`
- Minimum scaled size: 34px

### Easing
- Title entrance: `Easing.out(Easing.cubic)`
- Rule draw: `Easing.inOut(Easing.quad)`
- Background fade: linear clamp

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <GradientBackground fadeFrames={15} />
  <ParticleDrift count={18} />
  <Sequence from={15}>
    <TitleText text="Veo Section" />
  </Sequence>
  <Sequence from={30}>
    <HorizontalRule width={200} color="#5B9BD5" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Section",
  "particleCount": 18,
  "particleRadiusRange": [2, 4],
  "particleOpacity": 0.15,
  "particleSpeedRange": [1.5, 4.0],
  "ruleWidth": 200,
  "ruleColor": "#5B9BD5",
  "gradientTop": "#0B1D3A",
  "gradientBottom": "#162D50"
}
```

---
