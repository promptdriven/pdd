[Remotion] Wave Data Overlay

# Section 2.3: Wave Data Overlay

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:10 – 0:14

## Visual Description
An animated sine wave draws across the screen left-to-right over a dark gradient backdrop. Three blue accent dots spring into position along the wave crests. Below the wave, two stat callouts fade in sequentially — a coral film-reel icon labelled "Cinematic Footage" and a gold sparkle icon labelled "AI-Generated." The entire composition fades out at the end.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Solid `#0A1628`
- Gradient overlay: linear-gradient from bottom (`rgba(11,29,58,0.85)`) to top (`rgba(11,29,58,0)`)

### Chart/Visual Elements
- **Sine wave:** Stroke `#5B9BD5`, width 3px, amplitude 40px, wavelength 200px, centred at Y=540px
- **Accent dots:** 3 circles at X positions [480, 960, 1440], radius 6px, fill `#5B9BD5`, placed on wave crests
- **Stat callout 1:** Film-reel SVG icon (circle + satellite dots) in `#E8967A`, label "Cinematic Footage" at Y=700px
- **Stat callout 2:** Sparkle SVG icon in `#D4A843`, label "AI-Generated" at Y=760px

### Animation Sequence
1. **Frame 0–45 (0–1.5s):** Sine wave draws left-to-right via SVG stroke-dasharray (progress 0 → 1, linear)
2. **Frame 30–45 (1.0–1.5s):** Accent dots scale in (0 → 1) with spring physics (damping 10, stiffness 150, mass 0.5)
3. **Frame 45–75 (1.5–2.5s):** Stat callout 1 fades in (opacity 0 → 1, translateY 8px → 0) with `easeOutCubic`
4. **Frame 60–90 (2.0–3.0s):** Stat callout 2 fades in (opacity 0 → 1, translateY 8px → 0) with `easeOutCubic`
5. **Frame 105–120 (3.5–4.0s):** Entire composition fades out (opacity 1 → 0) with `easeInQuad`

### Typography
- Labels: Inter, 28px, weight 500, `#FFFFFF`
- Icon size: 24px

### Easing
- Wave draw: linear
- Dot entrance: spring (damping: 10, stiffness: 150, mass: 0.5)
- Callout entrance: `Easing.out(Easing.cubic)`
- Final fade: `Easing.in(Easing.quad)`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <GradientOverlay />
  <SineWavePath
    amplitude={40}
    wavelength={200}
    strokeColor="#5B9BD5"
    drawFrames={[0, 45]}
  />
  <Sequence from={30}>
    <AccentDots positions={[480, 960, 1440]} radius={6} />
  </Sequence>
  <Sequence from={45}>
    <StatCallout icon="filmReel" color="#E8967A" label="Cinematic Footage" />
  </Sequence>
  <Sequence from={60}>
    <StatCallout icon="sparkle" color="#D4A843" label="AI-Generated" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "wave": {
    "amplitude": 40,
    "wavelength": 200,
    "strokeWidth": 3,
    "strokeColor": "#5B9BD5",
    "centerY": 540
  },
  "accentDots": {
    "positions": [480, 960, 1440],
    "radius": 6,
    "color": "#5B9BD5"
  },
  "callouts": [
    { "icon": "filmReel", "color": "#E8967A", "label": "Cinematic Footage", "y": 700 },
    { "icon": "sparkle", "color": "#D4A843", "label": "AI-Generated", "y": 760 }
  ]
}
```

---
