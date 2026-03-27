[title:]

# Section 1.20: Try It Yourself — Handwritten Challenge Card

**Tool:** Title
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 8:04 - 8:12

## Visual Description

A challenge appears on screen in a handwritten style font. "Try it yourself." — casual, inviting, slightly provocative. This is the "homework" beat: the narrator challenges the viewer to test the thesis themselves.

The text appears with a hand-drawn feel — slightly imperfect, organic, as if scrawled on a whiteboard or notepad. The background is clean dark, with a subtle paper texture at very low opacity. Below the main challenge, a smaller instructional text reads: "Give your favorite LLM a hard coding problem as code, then as natural language. The natural language version will win."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Subtle paper texture: `#FFFFFF` at 0.02, noise grain overlay

### Chart/Visual Elements

#### Main Text
- "Try it yourself." — handwritten font (Caveat or similar), 64px, `#E2E8F0`
- Position: centered at (960, 440)
- Slight rotation: -1.5° (hand-drawn imperfection)
- Drawing animation: SVG path stroke reveal, as if being written

#### Instruction Text
- "Give your favorite LLM a hard coding problem as code," — Inter, 16px, regular (400), `#94A3B8` at 0.6
- "then as natural language." — Inter, 16px, regular (400), `#94A3B8` at 0.6
- "The natural language version will win." — Inter, 16px, semi-bold (600), `#E2E8F0` at 0.8
- Position: centered, starting at y: 560, 28px line spacing

#### Underline
- Hand-drawn style underline beneath "Try it yourself" — `#4A90D9` at 0.4, 2px, slightly wavy path

### Animation Sequence
1. **Frame 0-60 (0-2s):** Background with paper texture appears. "Try it yourself." begins writing — SVG stroke animation from left to right.
2. **Frame 60-90 (2-3s):** Underline draws beneath the text, slightly wavy.
3. **Frame 90-150 (3-5s):** Instruction text fades in line by line, 20 frames between each line.
4. **Frame 150-240 (5-8s):** Hold. The challenge sits on screen.

### Typography
- Challenge text: Caveat (or similar handwritten), 64px, `#E2E8F0`
- Instruction text: Inter, 16px, regular/semi-bold, `#94A3B8` / `#E2E8F0`
- Underline: hand-drawn path, `#4A90D9` at 0.4

### Easing
- Stroke write: `easeInOut(quad)` over 60 frames
- Underline: `easeOut(quad)` over 30 frames
- Text lines fade-in: `easeOut(quad)` over 20 frames each

## Narration Sync
> "Try it yourself. Take your favorite LLM, give it a hard coding problem as code, then give it the same problem described in natural language. The natural language version will win."

Note: This narration is part of the KEY INSIGHT subsection which bridges Parts 1 and 2. The visual challenge card appears as the narrator speaks.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <NoiseTexture color="#FFFFFF" opacity={0.02} grain={2} />

    {/* Handwritten challenge */}
    <Sequence from={0}>
      <StrokeReveal duration={60}>
        <Text
          text="Try it yourself."
          font="Caveat" size={64}
          color="#E2E8F0"
          x={960} y={440} align="center"
          rotation={-1.5}
        />
      </StrokeReveal>
    </Sequence>

    {/* Underline */}
    <Sequence from={60}>
      <DrawPath
        path={wavyUnderline}
        color="#4A90D9" opacity={0.4}
        strokeWidth={2} drawDuration={30}
      />
    </Sequence>

    {/* Instruction text */}
    <Sequence from={90}>
      <FadeIn duration={20}>
        <Text text="Give your favorite LLM a hard coding problem as code,"
          font="Inter" size={16} color="#94A3B8" opacity={0.6}
          x={960} y={560} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={110}>
      <FadeIn duration={20}>
        <Text text="then as natural language."
          font="Inter" size={16} color="#94A3B8" opacity={0.6}
          x={960} y={588} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={130}>
      <FadeIn duration={20}>
        <Text text="The natural language version will win."
          font="Inter" size={16} weight={600} color="#E2E8F0" opacity={0.8}
          x={960} y={628} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "style": "handwritten_challenge",
  "mainText": "Try it yourself.",
  "font": "Caveat",
  "instructions": [
    "Give your favorite LLM a hard coding problem as code,",
    "then as natural language.",
    "The natural language version will win."
  ],
  "backgroundColor": "#0A0F1A",
  "accentColor": "#4A90D9"
}
```

---
