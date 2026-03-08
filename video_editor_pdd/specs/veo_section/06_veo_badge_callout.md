[Remotion]

# Section 2.6: Veo Badge Callout

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:05 - 0:08

## Visual Description
An animated lower-third badge and subtitle overlay that appears over the forest canopy footage. A rounded pill-shaped badge reading "VEO GENERATED" slides in from the left, followed by the narration subtitle typing on below it. The badge has a translucent dark glass-morphism backing with a subtle green border glow, tying into the forest visuals behind it. A thin progress bar tracks across the bottom edge of the gradient strip.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent (overlaid on Veo clip)
- Grid lines: none

### Chart/Visual Elements
- Gradient bar: full-width, height 180px, anchored to bottom, gradient from transparent → #00000088
- Badge pill: positioned at (120, 870), 220x40px, background #1E293B with 60% opacity, border 1px #22C55E40, borderRadius 20px
  - Badge text: "VEO GENERATED" — color #22C55E, 14px, letter-spacing 2px, uppercase
  - Badge icon: small play-triangle (8px) to left of text, color #22C55E
- Subtitle text: positioned at (120, 930), max-width 1400px
  - "It uses Veo-generated clips with narration overlay."
- Progress bar: bottom edge (y=1076), height 4px, color #22C55E, width animates 0→100%

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Gradient bar fades in (opacity 0→0.85).
2. **Frame 8-22 (0.27-0.73s):** Badge pill slides in from left (x: -220 → 120) with slight bounce. Play icon spins 360° on entry.
3. **Frame 15-55 (0.5-1.83s):** Subtitle text types on character by character (~1.3 chars/frame).
4. **Frame 10-80 (0.33-2.67s):** Progress bar grows from left to right (width 0% → 100%).
5. **Frame 80-90 (2.67-3.0s):** All elements fade out (opacity 1→0).

### Typography
- Badge label: Inter SemiBold, 14px, green (#22C55E), tracking 2px, uppercase
- Subtitle: Inter Regular, 30px, white (#FFFFFF), letter-spacing 0.3px
- Text shadow: 0 2px 6px rgba(0,0,0,0.5)

### Easing
- Badge slide: `spring({ damping: 14, stiffness: 180 })`
- Progress bar: `linear`
- Text type-on: `linear`
- Fade out: `easeInCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={150} durationInFrames={90}>
  <AbsoluteFill style={{ justifyContent: "flex-end" }}>
    <GradientBar height={180} opacity={0.85} fadeIn={10} />
    <Sequence from={8}>
      <SlideIn from="left" distance={340} spring={{ damping: 14, stiffness: 180 }}>
        <Badge
          text="VEO GENERATED"
          icon="play"
          bgColor="#1E293B99"
          textColor="#22C55E"
          borderColor="#22C55E40"
          position={[120, 870]}
        />
      </SlideIn>
    </Sequence>
    <Sequence from={15}>
      <TypeOnText
        text="It uses Veo-generated clips with narration overlay."
        charsPerFrame={1.3}
        font="Inter"
        size={30}
        color="#FFFFFF"
        position={[120, 930]}
      />
    </Sequence>
    <Sequence from={10}>
      <ProgressBar y={1076} height={4} color="#22C55E" durationInFrames={70} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "narrationText": "It uses Veo-generated clips with narration overlay.",
  "badgeLabel": "VEO GENERATED",
  "badgeColor": "#22C55E",
  "typeSpeed": 1.3,
  "progressBarDuration": 70,
  "gradientBarHeight": 180
}
```

---
