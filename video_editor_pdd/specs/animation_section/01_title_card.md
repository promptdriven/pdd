[title:]

# Section 1.1: Animation Section Title Card

**Tool:** Remotion
**Duration:** ~3s (90 frames)
**Timestamp:** 0:00 - 0:03

## Visual Description
A cinematic title card introduces the Animation Section. A deep navy-to-blue gradient fills the screen while 60 floating particle dots drift upward. The main title "Animation Section" slides up from below with bold white type, followed by a glowing blue accent line that expands horizontally from center, and finally a muted subtitle "Integration Test Video" fades in beneath.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Linear gradient 180deg from #0A1628 (top) to #1E3A8A (bottom)
- Noise texture overlay at 5% opacity (SVG fractalNoise filter)

### Chart/Visual Elements
- **Particle system:** 60 dots, sizes 2-6px, color #3B82F6 at 30% opacity, drifting upward at speed 2
- **Title text:** "Animation Section" centered at Y=460, white #FFFFFF
- **Accent line:** Horizontal bar at Y=530, 400px wide x 4px tall, color #3B82F6 with 40px blur glow
- **Subtitle text:** "Integration Test Video" centered at Y=580, color #94A3B8

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background gradient fades in from black (opacity 0 to 1)
2. **Frame 15-45 (0.5-1.5s):** Title text slides up from Y=500 to Y=460, opacity 0 to 1
3. **Frame 30-60 (1.0-2.0s):** Accent line scales from width 0 to 400px, expanding from center
4. **Frame 45-75 (1.5-2.5s):** Subtitle fades in, opacity 0 to 1
5. **Frame 0-90 (continuous):** Particles drift upward throughout

### Typography
- Title: Inter, 96px, bold, #FFFFFF, letter-spacing -2px
- Subtitle: Inter, 32px, normal, #94A3B8, letter-spacing 0px

### Easing
- Background fade: `linear`
- Title slide: `easeOutCubic`
- Accent line expand: `easeInOutCubic`
- Subtitle fade: `easeOutQuad`

## Narration Sync
> "This is the first section of the integration test video."

This visual spans the beginning of Segment 1 (0.0s-2.9s). The title card establishes context before the narration begins and persists through the first sentence.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ background: 'linear-gradient(180deg, #0A1628, #1E3A8A)', opacity: backgroundOpacity }}>
    <NoiseOverlay opacity={0.05} />
    <ParticleSystem count={60} speed={2} color="#3B82F6" />
    <Sequence from={15}>
      <TitleText text="Animation Section" />
    </Sequence>
    <Sequence from={30}>
      <AccentLine width={400} color="#3B82F6" />
    </Sequence>
    <Sequence from={45}>
      <SubtitleText text="Integration Test Video" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Animation Section",
  "subtitle": "Integration Test Video",
  "particles": { "count": 60, "speed": 2, "minSize": 2, "maxSize": 6 }
}
```

---
