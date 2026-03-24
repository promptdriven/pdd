[title:]

# Section 1.17: Try It Yourself — Handwritten Challenge Card

**Tool:** Title
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 5:58 - 6:04

## Visual Description

A clean slate with a handwritten-style challenge appearing on screen. "Try it yourself." writes on in a script font, as if drawn by hand — the pen strokes animate character by character. Below it, smaller supporting text fades in: "Take your favorite LLM. Give it a hard coding problem as code. Then give it the same problem in natural language. The natural language version will win."

The handwritten style breaks from the precise technical aesthetic of the rest of the section — this is personal, direct, a challenge from narrator to viewer. The background is the familiar deep navy-black but the text has a warm human quality.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines — clean slate

### Chart/Visual Elements

#### Handwritten Challenge
- "Try it yourself." — handwriting-style font (Caveat or similar), 48px, `#E2E8F0` at 0.9
- Centered at (960, 440)
- Animated with stroke-dashoffset to simulate handwriting
- Subtle warm tint: `#FBBF24` at 0.05 glow behind text

#### Supporting Text
- "Take your favorite LLM." — Inter, 16px, `#94A3B8` at 0.5, centered at y: 540
- "Give it a hard coding problem as code," — Inter, 16px, `#94A3B8` at 0.5, y: 570
- "then as natural language." — Inter, 16px, `#94A3B8` at 0.5, y: 600
- "The natural language version will win." — Inter, 16px, semi-bold (600), `#E2E8F0` at 0.7, y: 650

#### Pen Cursor (optional)
- Small circle 3px, `#E2E8F0` at 0.4, follows the handwriting path
- Disappears after writing completes

### Animation Sequence
1. **Frame 0-30 (0-1s):** Previous visual fades. Clean slate.
2. **Frame 30-90 (1-3s):** "Try it yourself." writes on character by character, handwriting style. Pen cursor traces the path.
3. **Frame 90-110 (3-3.67s):** Brief hold after handwriting completes. Pen cursor fades.
4. **Frame 110-150 (3.67-5s):** Supporting text lines fade in sequentially, 10 frames apart.
5. **Frame 150-180 (5-6s):** Hold on complete challenge. Last line ("will win") pulses once.

### Typography
- Handwritten challenge: Caveat (or similar script font), 48px, `#E2E8F0` at 0.9
- Supporting text: Inter, 16px, `#94A3B8` at 0.5
- Final line: Inter, 16px, semi-bold (600), `#E2E8F0` at 0.7

### Easing
- Handwrite stroke: `easeInOut(quad)` per character, 4 frames each
- Pen cursor: follows stroke path precisely
- Supporting text fade: `easeOut(quad)` over 15 frames, staggered 10 frames
- Final line pulse: `easeInOut(sine)` once, 20 frames

## Narration Sync
> "Try it yourself. Take your favorite LLM, give it a hard coding problem as code, then give it the same problem described in natural language. The natural language version will win."

Segment: (end of part1 narration)

- **5:58** ("Try it yourself"): Handwriting begins
- **6:00** ("Take your favorite LLM"): Supporting text starts
- **6:04** ("will win"): Final line emphasis, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Handwritten challenge */}
    <Sequence from={30}>
      <HandwriteText
        text="Try it yourself."
        font="Caveat" size={48}
        color="#E2E8F0" opacity={0.9}
        x={960} y={440} align="center"
        strokeDuration={60}
        cursor={{ size: 3, color: '#E2E8F0', opacity: 0.4 }}
        glow={{ color: '#FBBF24', opacity: 0.05 }} />
    </Sequence>

    {/* Supporting text */}
    <Sequence from={110}>
      <StaggeredFadeIn stagger={10} duration={15}>
        <Text text="Take your favorite LLM."
          font="Inter" size={16} color="#94A3B8" opacity={0.5}
          x={960} y={540} align="center" />
        <Text text="Give it a hard coding problem as code,"
          font="Inter" size={16} color="#94A3B8" opacity={0.5}
          x={960} y={570} align="center" />
        <Text text="then as natural language."
          font="Inter" size={16} color="#94A3B8" opacity={0.5}
          x={960} y={600} align="center" />
      </StaggeredFadeIn>
    </Sequence>

    {/* Final line with emphasis */}
    <Sequence from={140}>
      <FadeIn duration={15}>
        <PulseOnce duration={20}>
          <Text text="The natural language version will win."
            font="Inter" size={16} weight={600}
            color="#E2E8F0" opacity={0.7}
            x={960} y={650} align="center" />
        </PulseOnce>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": "1.end",
  "style": "handwritten_challenge",
  "challenge": "Try it yourself.",
  "supportingText": [
    "Take your favorite LLM.",
    "Give it a hard coding problem as code,",
    "then as natural language.",
    "The natural language version will win."
  ],
  "font": "Caveat",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": []
}
```

---
