[title:]

# Section 5.10: Transition Out — Bridge to Next Section

**Tool:** Title
**Duration:** ~4s
**Timestamp:** 1:51 - 1:55

## Visual Description
A brief transition beat that bridges Part 5 into the next section. The screen is dark — the quote card has faded out — and a single line of text appears center-screen, setting up the practical turn: a forward-looking prompt that the next section will answer.

The text "Now, you don't work on socks." appears in clean white typography, slightly smaller than a title card. It's a pivot line — acknowledging the metaphor is over and grounding the viewer back in software. The tone is wry, direct, almost a knowing aside.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines, no decorative elements

### Chart/Visual Elements
- None — text only

### Animation Sequence
1. **Frame 0-20 (0-0.7s):** Background holds at `#0A0F1A`. Brief beat of silence/darkness.
2. **Frame 20-50 (0.7-1.7s):** Text fades in with slight scale (`0.95→1.0`) and opacity (`0→1`).
3. **Frame 50-100 (1.7-3.3s):** Hold on text.
4. **Frame 100-120 (3.3-4s):** Text and background fade to black.

### Typography
- Text: Inter, 28px, medium (500), `#E2E8F0`
- Centered horizontally and vertically

### Easing
- Text fade-in: `easeOutQuad` over 20 frames
- Text scale: `easeOutCubic` over 20 frames
- Fade to black: `easeInQuad` over 20 frames

## Narration Sync
> "Now, you don't work on socks."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Transition text */}
    <Sequence from={20}>
      <ScaleAndFade
        fromScale={0.95} toScale={1.0}
        durationInFrames={20} easing="easeOutCubic">
        <Text text="Now, you don't work on socks."
          font="Inter" size={28} weight={500}
          color="#E2E8F0" align="center" />
      </ScaleAndFade>
    </Sequence>

    {/* Fade to black */}
    <Sequence from={100}>
      <FadeOut durationInFrames={20} easing="easeInQuad" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "transition_card",
  "text": "Now, you don't work on socks.",
  "backgroundColor": "#0A0F1A",
  "durationSeconds": 4,
  "narrationSegments": ["part5_compound_returns_011"]
}
```
