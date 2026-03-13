[title:] Veo Section End Card

# Section 2.8: Section End Card

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:19 – 0:22

## Visual Description
A closing card that bookends the Veo Section. The deep ocean-blue gradient from the title card returns. A completion ring (circular progress indicator) draws clockwise to 100%, followed by a checkmark icon that pops in at centre. The section label "Veo Section Complete" fades in below with a subtle horizontal rule expanding outward beneath it. Soft bokeh particles drift in the background throughout.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Linear gradient from `#0B1D3A` (top) to `#162D50` (bottom)

### Chart/Visual Elements
- **Completion ring:** 80px radius, 4px stroke, colour `#5B9BD5`, centred at (960, 460), draws clockwise 0° → 360°
- **Checkmark icon:** 32px, stroke `#40916C`, centred within completion ring
- **Section label:** "Veo Section Complete" centred at Y=600px
- **Horizontal rule:** 160px wide, 2px tall, colour `#5B9BD5`, 16px below label, draws from centre outward
- **Bokeh particles:** 12 circles (radius 3–8px, opacity 0.08–0.15) with slow random drift and gaussian blur 3px

### Animation Sequence
1. **Frame 0–10 (0–0.33s):** Background gradient fades in (opacity 0 → 1)
2. **Frame 0–90 (0–3.0s):** Bokeh particles drift continuously (random directions, 0.5–2.0 px/frame)
3. **Frame 10–40 (0.33–1.33s):** Completion ring draws clockwise (0° → 360°) with `easeInOutCubic`
4. **Frame 40–55 (1.33–1.83s):** Checkmark icon scales in (0 → 1) with `easeOut(back(1.5))` bounce
5. **Frame 50–70 (1.67–2.33s):** "Veo Section Complete" fades in (opacity 0 → 1, translateY 10px → 0) with `easeOutCubic`
6. **Frame 60–80 (2.0–2.67s):** Horizontal rule scales outward from centre (scaleX 0 → 1) with `easeInOutQuad`

### Typography
- Section label: Inter, 36px, weight 600, `#FFFFFF`
- Minimum scaled size: 24px

### Easing
- Ring draw: `Easing.inOut(Easing.cubic)`
- Checkmark pop: `Easing.out(Easing.back(1.5))`
- Label entrance: `Easing.out(Easing.cubic)`
- Rule draw: `Easing.inOut(Easing.quad)`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <GradientBackground fadeFrames={10} />
  <BokehParticles count={12} />
  <Sequence from={10}>
    <CompletionRing radius={80} stroke={4} color="#5B9BD5" />
  </Sequence>
  <Sequence from={40}>
    <CheckmarkIcon size={32} color="#40916C" />
  </Sequence>
  <Sequence from={50}>
    <SectionLabel text="Veo Section Complete" />
  </Sequence>
  <Sequence from={60}>
    <ExpandingRule width={160} color="#5B9BD5" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "completionRing": {
    "radius": 80,
    "strokeWidth": 4,
    "color": "#5B9BD5",
    "center": [960, 460]
  },
  "checkmark": {
    "size": 32,
    "color": "#40916C"
  },
  "label": "Veo Section Complete",
  "rule": {
    "width": 160,
    "height": 2,
    "color": "#5B9BD5"
  },
  "bokeh": {
    "count": 12,
    "radiusRange": [3, 8],
    "opacityRange": [0.08, 0.15],
    "blur": 3
  },
  "gradientTop": "#0B1D3A",
  "gradientBottom": "#162D50"
}
```

---
