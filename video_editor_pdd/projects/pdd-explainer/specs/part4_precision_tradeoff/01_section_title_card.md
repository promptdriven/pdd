[title:]

# Section 4.1: The Precision Tradeoff — Section Title Card

**Tool:** Title
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 0:00 - 0:08

## Visual Description

A section title card introducing Part 4. "THE PRECISION" appears in large bold weight, then "TRADEOFF" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of an inverse curve sits at very low opacity — a descending hyperbola from upper-left to lower-right, foreshadowing the tests-vs-precision thesis. Background is deep navy-black consistent with the overall visual language.

The title holds briefly as the narrator begins "Let's talk about precision. Because there's a subtle tradeoff..." then fades out as the split screen establishes.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE PRECISION" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "TRADEOFF" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 280px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 4" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (inverse curve)
- Inverse hyperbola: `#D9944A` at 0.04, 1.5px stroke, from upper-left to lower-right
- Faint grid squares along curve path: `#4A90D9` at 0.03

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-35 (0.5-1.17s):** "PART 4" label fades in. Ghost inverse curve draws with stroke-dashoffset.
3. **Frame 35-55 (1.17-1.83s):** "THE PRECISION" types on character-by-character (2 frames per character).
4. **Frame 55-65 (1.83-2.17s):** Horizontal rule draws from center outward.
5. **Frame 65-85 (2.17-2.83s):** "TRADEOFF" fades in with 10px upward slide.
6. **Frame 85-180 (2.83-6s):** Hold. Ghost curve pulses subtly.
7. **Frame 180-240 (6-8s):** Title and elements fade out, transitioning to split screen.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "TRADEOFF" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost curve draw: `easeInOut(cubic)` over 25 frames
- Curve pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."

Segment: `part4_precision_tradeoff_001` (partial)

- **0.00s** (seg 001): Title card begins fade-in
- **6.00s**: Title begins fade-out
- **8.00s**: Fully faded, split screen takes over

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost inverse curve */}
    <Sequence from={15}>
      <StrokeDraw duration={25}>
        <InverseCurve
          color="#D9944A" opacity={0.04}
          strokeWidth={1.5}
        />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 4" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE PRECISION */}
    <Sequence from={35}>
      <TypeWriter text="THE PRECISION" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={55}>
      <DrawLine from={[820, 505]} to={[1100, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: TRADEOFF */}
    <Sequence from={65}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="TRADEOFF" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Fade out */}
    <Sequence from={180}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 4,
  "sectionLabel": "PART 4",
  "titleLine1": "THE PRECISION",
  "titleLine2": "TRADEOFF",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "inverse_curve", "color": "#D9944A", "role": "precision_tradeoff_preview" }
  ],
  "narrationSegments": ["part4_precision_tradeoff_001"]
}
```

---
