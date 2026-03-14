[title:]

# Section 1.1: Title Card

**Tool:** Remotion
**Duration:** ~1.5s (45 frames @ 30fps)
**Timestamp:** 0:00 - 0:03

## Visual Description
A cinematic section opener on a dark navy background. The title "Animation Section" fades in at center screen with a subtle scale-up effect. A thin white accent line expands horizontally outward from center beneath the title. Finally, the subtitle "Integration Test" fades in below the accent line. The card holds briefly before the next visual begins.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy (#0F172A), solid fill

### Chart/Visual Elements
- **Title text:** "Animation Section" — centered horizontally, offset 40px above vertical center
- **Accent line:** Horizontal white line (rgba(255,255,255,0.8)), 2px tall, expands from 0px to 400px width, centered, positioned 16px below title baseline
- **Subtitle text:** "Integration Test" — centered horizontally, 24px below accent line

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Title fades in (opacity 0 → 1) and scales up (0.95 → 1.0)
2. **Frame 9-24 (0.3-0.8s):** Accent line expands outward from center (width 0 → 400px)
3. **Frame 15-30 (0.5-1.0s):** Subtitle fades in (opacity 0 → 1)
4. **Frame 30-45 (1.0-1.5s):** Hold — all elements at full visibility

### Typography
- Title: Inter 700, 72px, white (#FFFFFF)
- Subtitle: Inter 400, 28px, slate (#CBD5E1)

### Easing
- Title fade/scale: `linear` (implicit Remotion interpolation)
- Accent line expand: `linear`
- Subtitle fade: `linear`

## Narration Sync
> (No narration during title card — precedes first narration beat)

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
  <Sequence from={0} durationInFrames={45}>
    <TitleText />
  </Sequence>
  <Sequence from={9} durationInFrames={36}>
    <AccentLine />
  </Sequence>
  <Sequence from={15} durationInFrames={30}>
    <SubtitleText />
  </Sequence>
</AbsoluteFill>
```

## Data Points
```json
{
  "title": "Animation Section",
  "subtitle": "Integration Test"
}
```

---
