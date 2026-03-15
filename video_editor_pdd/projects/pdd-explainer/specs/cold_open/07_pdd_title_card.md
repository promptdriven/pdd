[title:]

# Section 0.7: PDD Title Card

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 1:05 - 1:20

## Visual Description
The concentric rings from the previous scene collapse inward toward the center point and transform into the title card. The rings compress into a single horizontal accent line, and the center glow expands into the title text "Prompt-Driven Development." The subtitle "Why You're Still Darning Socks" fades in below. This is the formal title reveal — clean, weighted, and cinematic. The background is dark with a very subtle radial gradient suggesting depth.

Below the subtitle, two thin horizontal rules frame the subtitle. The overall composition is vertically centered and balanced, in the 3Blue1Brown tradition of mathematical elegance applied to typography.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient from center `#0F172A` to edges `#020617`
- Grid lines: None

### Chart/Visual Elements
- **Title Text:** "Prompt-Driven Development" — white `#FFFFFF`, centered at (960, 460)
- **Accent Line (upper):** Horizontal rule, `#4A90D9` at 60% opacity, centered at Y=510, 400px wide x 1.5px tall
- **Subtitle Text:** "Why You're Still Darning Socks" — muted `#94A3B8`, centered at (960, 560)
- **Accent Line (lower):** Horizontal rule, `#4A90D9` at 40% opacity, centered at Y=600, 280px wide x 1px tall
- **Ambient Particles:** 8-12 small dots (2-3px), `#4A90D9` at 10-20% opacity, drifting slowly upward in background. Provides subtle life without distraction.

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Previous scene's concentric rings collapse inward (radii shrink to 0) and merge into the center point. Center glow intensifies (opacity 0.6→1.0, radius 8→40px).
2. **Frame 30-60 (1.0-2.0s):** Center glow morphs into title text — the glow elongates horizontally (scaleX: 1→20, scaleY: 1→0.5) and cross-fades with the title text fading in. The glow dissipates as the text solidifies.
3. **Frame 60-90 (2.0-3.0s):** Upper accent line draws from center outward (width: 0→400px). Symmetric expansion.
4. **Frame 90-120 (3.0-4.0s):** Subtitle text fades in (opacity 0→1) with a gentle 8px upward drift.
5. **Frame 120-140 (4.0-4.67s):** Lower accent line draws from center outward (width: 0→280px).
6. **Frame 140-180 (4.67-6.0s):** Ambient particles begin drifting upward. All elements at final state.
7. **Frame 180-450 (6.0-15.0s):** Hold. Title card fully visible. Particles continue drifting. This hold allows the title to register and provides space for the narration transition.

### Typography
- Title: Inter, 64px, bold (700), `#FFFFFF`, letter-spacing: 2px
- Subtitle: Inter, 26px, regular (400), `#94A3B8`, letter-spacing: 1px

### Easing
- Ring collapse: `easeIn(cubic)` — accelerates inward
- Glow morph: `easeInOut(quad)`
- Title fade-in: `easeOut(quad)`
- Accent line draw: `easeOut(cubic)`
- Subtitle fade/drift: `easeOut(quad)`
- Particle drift: `linear` (continuous, no easing)

## Narration Sync
> (No narration during title card — musical beat / ambient tone. Transition moment before the 30-second demo begins.)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  <RadialGradientBg center="#0F172A" edge="#020617" />

  {/* Ring Collapse from Previous Scene */}
  <Sequence from={0} durationInFrames={30}>
    <CollapsingRings
      radii={[120, 220, 340]}
      colors={["#D9944A", "#EF4444", "#F59E0B"]}
      center={[960, 540]}
    />
  </Sequence>

  {/* Glow → Title Morph */}
  <Sequence from={30}>
    <GlowToTextMorph
      glowColor="#4A90D9"
      center={[960, 460]}
      text="Prompt-Driven Development"
      durationInFrames={30}
    />
  </Sequence>

  {/* Upper Accent Line */}
  <Sequence from={60}>
    <ExpandingLine
      y={510}
      targetWidth={400}
      color="#4A90D9"
      opacity={0.6}
      thickness={1.5}
      durationInFrames={30}
    />
  </Sequence>

  {/* Subtitle */}
  <Sequence from={90}>
    <FadeInDrift text="Why You're Still Darning Socks" y={560} drift={-8} durationInFrames={30}>
      <TextStyle font="Inter" size={26} color="#94A3B8" />
    </FadeInDrift>
  </Sequence>

  {/* Lower Accent Line */}
  <Sequence from={120}>
    <ExpandingLine y={600} targetWidth={280} color="#4A90D9" opacity={0.4} thickness={1} durationInFrames={20} />
  </Sequence>

  {/* Ambient Particles */}
  <Sequence from={140}>
    <AmbientParticles
      count={10}
      color="#4A90D9"
      opacityRange={[0.1, 0.2]}
      sizeRange={[2, 3]}
      driftDirection="up"
      speed={0.3}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "title": "Prompt-Driven Development",
  "subtitle": "Why You're Still Darning Socks",
  "titlePosition": [960, 460],
  "subtitlePosition": [960, 560],
  "titleColor": "#FFFFFF",
  "subtitleColor": "#94A3B8",
  "accentColor": "#4A90D9",
  "upperLine": { "y": 510, "width": 400, "opacity": 0.6, "thickness": 1.5 },
  "lowerLine": { "y": 600, "width": 280, "opacity": 0.4, "thickness": 1 },
  "background": {
    "center": "#0F172A",
    "edge": "#020617"
  },
  "particles": {
    "count": 10,
    "color": "#4A90D9",
    "opacityRange": [0.1, 0.2],
    "sizeRange": [2, 3]
  },
  "collapsingRings": [
    { "radius": 120, "color": "#D9944A" },
    { "radius": 220, "color": "#EF4444" },
    { "radius": 340, "color": "#F59E0B" }
  ]
}
```

---
