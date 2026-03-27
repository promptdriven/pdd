[title:]

# Section 4.7: Key Insight — "More Tests, Less Prompt"

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 1:04 - 1:08

## Visual Description

A typographic emphasis card delivering the core takeaway of Part 4's first half. Clean, centered text on a dark background — a "pull quote" moment that lets the insight land.

The primary text reads: **"More tests, less prompt."** Large, bold, white. Below it in smaller text: **"The walls do the precision work."** This second line uses the amber accent color to tie back to the injection mold metaphor.

The background has a subtle gradient glow — blue on the left (tests) fading to amber on the right (prompt/walls) — echoing the zones from the precision tradeoff curve. The text pulses once with a gentle glow before holding.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Gradient underlay: radial gradient from `#4A90D9` at 0.04 (left) to `#D9944A` at 0.04 (right)

### Chart/Visual Elements

#### Primary Text
- "More tests, less prompt." — Inter, 56px, bold (700), `#E2E8F0`, centered at y: 480
- Text glow: `#FFFFFF` at 0.06, 20px blur, pulses once

#### Secondary Text
- "The walls do the precision work." — Inter, 28px, regular (400), `#D9944A` at 0.7, centered at y: 560

#### Decorative
- Thin horizontal rule above primary text: 200px, `#334155` at 0.3, y: 440
- Thin horizontal rule below secondary text: 200px, `#334155` at 0.3, y: 600

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Background gradient fades in. Rules draw from center outward.
2. **Frame 20-50 (0.67-1.67s):** Primary text fades in with subtle scale 0.97→1.0. Text glow pulses once.
3. **Frame 50-70 (1.67-2.33s):** Secondary text fades in.
4. **Frame 70-100 (2.33-3.33s):** Hold. The insight sits.
5. **Frame 100-120 (3.33-4s):** Fade out.

### Typography
- Primary: Inter, 56px, bold (700), `#E2E8F0`
- Secondary: Inter, 28px, regular (400), `#D9944A` at 0.7

### Easing
- Primary text: `easeOut(cubic)` scale + fade over 20 frames
- Text glow pulse: `easeInOut(sine)` over 30 frames
- Secondary text: `easeOut(quad)` fade over 20 frames
- Rules draw: `easeInOut(quad)` over 15 frames
- Fade out: `easeIn(quad)` over 20 frames

## Narration Sync
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segment: End of `part4_precision_tradeoff_003` / gap before `part4_precision_tradeoff_004`

- **62.00s**: Text appears — "The more walls you have"
- **64.52s** (seg 003 ends): Hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Background gradient */}
    <RadialGradient
      leftColor="#4A90D9" rightColor="#D9944A"
      opacity={0.04}
    />

    {/* Upper rule */}
    <Sequence from={0}>
      <DrawLine from={[860, 440]} to={[1060, 440]}
        color="#334155" opacity={0.3} width={1}
        drawDuration={15} fromCenter />
    </Sequence>

    {/* Primary text */}
    <Sequence from={20}>
      <ScaleIn from={0.97} duration={20}>
        <FadeIn duration={20}>
          <Text text="More tests, less prompt."
            font="Inter" size={56} weight={700}
            color="#E2E8F0" x={960} y={480} align="center" />
        </FadeIn>
      </ScaleIn>
      <GlowPulse color="#FFFFFF" opacity={0.06}
        blur={20} duration={30} delay={10} />
    </Sequence>

    {/* Secondary text */}
    <Sequence from={50}>
      <FadeIn duration={20}>
        <Text text="The walls do the precision work."
          font="Inter" size={28} weight={400}
          color="#D9944A" opacity={0.7}
          x={960} y={560} align="center" />
      </FadeIn>
    </Sequence>

    {/* Lower rule */}
    <Sequence from={0}>
      <DrawLine from={[860, 600]} to={[1060, 600]}
        color="#334155" opacity={0.3} width={1}
        drawDuration={15} fromCenter />
    </Sequence>

    {/* Fade out */}
    <Sequence from={100}>
      <FadeOut duration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "key_insight",
  "chartId": "key_insight_walls",
  "primaryText": "More tests, less prompt.",
  "secondaryText": "The walls do the precision work.",
  "accentColors": {
    "tests": "#4A90D9",
    "walls": "#D9944A"
  },
  "narrationSegments": ["part4_precision_tradeoff_003"]
}
```

---
