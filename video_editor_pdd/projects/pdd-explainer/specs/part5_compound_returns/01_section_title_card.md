[title:]

# Section 5.1: Compound Returns — Section Title Card

**Tool:** Title
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

A bold section title card introducing Part 5. The text "COMPOUND RETURNS" appears in large, clean typography against a deep navy-black background. Below, a subtle tagline: "Why the economics compound for you." The title animates in with a confident fade-and-scale, establishing the shift from individual examples to systemic implications.

A faint grid pattern pulses softly in the background — suggesting the mathematical/economic framing of this section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: faint `#1A2540` at 0.08 opacity, 80px spacing, pulsing

### Chart/Visual Elements

#### Title Text
- "COMPOUND RETURNS" — centered, Inter, 72px, bold (800), `#E2E8F0` at 0.95
- Tracking: 6px letter-spacing
- Positioned at vertical center minus 40px

#### Tagline
- "Why the economics compound for you." — Inter, 22px, regular (400), `#94A3B8` at 0.7
- Positioned 60px below title

#### Background Grid
- Grid lines: 1px, `#1A2540` at 0.08
- Pulse: opacity oscillates 0.04–0.12 on 90-frame sine cycle
- Adds subtle mathematical texture

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Black. Grid fades in softly.
2. **Frame 15-60 (0.5-2s):** "COMPOUND RETURNS" scales from 0.85 → 1.0 and fades from 0 → 1. `easeOutCubic`.
3. **Frame 60-90 (2-3s):** Tagline fades in. `easeOutQuad`.
4. **Frame 90-210 (3-7s):** Hold. Grid pulses softly.
5. **Frame 210-240 (7-8s):** Everything fades out. `easeInQuad`.

### Typography
- Title: Inter, 72px, bold (800), `#E2E8F0`, tracking 6px
- Tagline: Inter, 22px, regular (400), `#94A3B8` at 0.7

### Easing
- Title scale-in: `easeOut(cubic)` over 45 frames
- Tagline fade: `easeOut(quad)` over 30 frames
- Grid pulse: `easeInOut(sine)` on 90-frame cycle
- Fade-out: `easeIn(quad)` over 30 frames

## Narration Sync
> "Now let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."

Segment: `part5_compound_returns_001`

- **0:00** ("Now let's zoom out"): Title card appears
- **0:04** ("numbers you just saw"): Hold on title
- **0:07** ("staggering"): Begin fade-out transition

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <PulsingGrid spacing={80} color="#1A2540"
      opacityRange={[0.04, 0.12]} period={90} />

    <Sequence from={15}>
      <ScaleIn from={0.85} to={1.0} duration={45}>
        <FadeIn duration={45}>
          <Text text="COMPOUND RETURNS"
            font="Inter" size={72} weight={800}
            color="#E2E8F0" opacity={0.95}
            letterSpacing={6}
            x={960} y={500} align="center" />
        </FadeIn>
      </ScaleIn>
    </Sequence>

    <Sequence from={60}>
      <FadeIn duration={30}>
        <Text text="Why the economics compound for you."
          font="Inter" size={22} weight={400}
          color="#94A3B8" opacity={0.7}
          x={960} y={570} align="center" />
      </FadeIn>
    </Sequence>

    <Sequence from={210}>
      <FadeOut duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionId": "part5_compound_returns",
  "title": "COMPOUND RETURNS",
  "tagline": "Why the economics compound for you.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part5_compound_returns_001"]
}
```

---
