[Remotion]

# Section 2.11: Veo Badge Reprise

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:30 - 0:33

## Visual Description
The Veo badge returns, this time in a larger format at center-screen over a dimmed version of the forest canopy footage. The badge expands from the compact pill into a full branded lockup: a large "Veo" wordmark with a tagline "AI-Generated Video" beneath it. A ring of subtle particle dots orbits the badge, reinforcing the AI-generation theme.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Forest canopy footage at 30% brightness (dimmed overlay rgba(0, 0, 0, 0.7))

### Chart/Visual Elements
- Dimming overlay: Full-frame rgba(0, 0, 0, 0.7) on top of footage
- Veo wordmark: "Veo" — centered at (960, 480), large display text
- Tagline: "AI-Generated Video" — centered at (960, 560)
- Particle ring: 24 small circles (4px diameter), arranged in a 200px radius circle around the wordmark
  - Color: #F59E0B at 40% opacity
  - Each particle slightly different size (3-5px)
- Accent line: 120px horizontal rule below tagline, centered, #F59E0B

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Dimming overlay fades in from 0% to 70% opacity.
2. **Frame 10-30 (0.33-1s):** Veo wordmark scales in from 0.5 to 1.0, opacity 0% to 100%.
3. **Frame 25-40 (0.83-1.33s):** Tagline fades in from 0% to 100% opacity, slides up from Y=580 to Y=560.
4. **Frame 35-45 (1.17-1.5s):** Accent line expands from 0px to 120px width.
5. **Frame 30-75 (1-2.5s):** Particle ring fades in and orbits slowly (full rotation over 90 frames). Each particle has slight radial oscillation.
6. **Frame 75-90 (2.5-3s):** All elements fade out to 0% opacity.

### Typography
- Veo wordmark: Inter Black, 96px, #FFFFFF, letter-spacing 4px
- Tagline: Inter Light, 24px, #F59E0B, letter-spacing 2px
- No additional text

### Easing
- Wordmark scale: `easeOutBack`
- Tagline fade/slide: `easeOutCubic`
- Accent line expand: `easeInOutQuad`
- Particle orbit: `linear` (constant rotation)
- Fade out: `easeInQuad`

## Narration Sync
> (No narration — branded interstitial beat)

## Code Structure (Remotion)
```typescript
<Sequence from={900} durationInFrames={90}>
  <DimmingOverlay opacity={0.7} />
  <Sequence from={10}>
    <ScaleInText text="Veo" fontSize={96} font="Inter Black" />
  </Sequence>
  <Sequence from={25}>
    <FadeInTagline text="AI-Generated Video" color="#F59E0B" />
  </Sequence>
  <Sequence from={35}>
    <ExpandingRule width={120} color="#F59E0B" />
  </Sequence>
  <Sequence from={30}>
    <ParticleRing count={24} radius={200} color="#F59E0B" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "wordmark": "Veo",
  "tagline": "AI-Generated Video",
  "accentColor": "#F59E0B",
  "particleCount": 24,
  "particleRadius": 200
}
```

---
