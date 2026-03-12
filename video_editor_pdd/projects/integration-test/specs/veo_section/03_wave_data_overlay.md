[Remotion]

# Section 2.3: Wave Data Overlay

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:08 - 0:12

## Visual Description
An animated data-visualization overlay that transitions out of the ocean footage. A stylized sine-wave line animates across the screen from left to right, representing the rhythm of ocean waves. Below it, two stat callouts fade in sequentially: "Cinematic Footage" with a film-reel icon and "AI-Generated" with a sparkle icon. The background is a translucent dark gradient over the lingering ocean color palette, giving a polished lower-third feel.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: semi-transparent gradient #0B1D3A at 85% opacity → transparent top
- No grid lines

### Chart/Visual Elements
- **Sine wave line:** Stroke color #5B9BD5, stroke width 3px, amplitude 40px, wavelength 200px, drawn left-to-right across full width at vertical center (y=540)
- **Stat callout 1:** Film-reel icon (24px, #E8967A) + "Cinematic Footage" label, positioned at (300, 700)
- **Stat callout 2:** Sparkle icon (24px, #D4A843) + "AI-Generated" label, positioned at (300, 760)
- **Accent dots:** 3 small circles (r=6px) along the sine wave crest at x=480, x=960, x=1440, color #5B9BD5

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Sine wave draws left-to-right with path-tracing animation
2. **Frame 30-45 (1-1.5s):** Accent dots scale in (0→1) at their positions along the crest
3. **Frame 45-75 (1.5-2.5s):** Stat callout 1 fades in and slides up 8px
4. **Frame 60-90 (2-3s):** Stat callout 2 fades in and slides up 8px
5. **Frame 90-120 (3-4s):** Hold; entire composition fades out in last 15 frames

### Typography
- Stat labels: Inter Medium, 28px, #FFFFFF
- Icon size: 24x24px

### Easing
- Sine wave draw: `linear`
- Dot scale-in: `easeOutBack`
- Stat callout fade/slide: `easeOutCubic`
- Final fade-out: `easeInQuad`

## Narration Sync
> (Tail end of: "This is the second section of the integration test video." — visual bridge between narration beats)

## Code Structure (Remotion)
```typescript
<Sequence from={240} durationInFrames={120}>
  <GradientOverlay color="#0B1D3A" opacity={0.85} />
  <Sequence from={0}>
    <SineWavePath
      color="#5B9BD5"
      strokeWidth={3}
      amplitude={40}
      wavelength={200}
    />
  </Sequence>
  <Sequence from={30}>
    <AccentDots positions={[480, 960, 1440]} color="#5B9BD5" />
  </Sequence>
  <Sequence from={45}>
    <StatCallout icon="film-reel" label="Cinematic Footage" color="#E8967A" />
  </Sequence>
  <Sequence from={60}>
    <StatCallout icon="sparkle" label="AI-Generated" color="#D4A843" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "stats": [
    { "icon": "film-reel", "label": "Cinematic Footage", "color": "#E8967A" },
    { "icon": "sparkle", "label": "AI-Generated", "color": "#D4A843" }
  ],
  "wave": {
    "amplitude": 40,
    "wavelength": 200,
    "color": "#5B9BD5"
  }
}
```

---
