[title:]

# Section 1.15: Key Insight Stillness — The 3B1B Beat

**Tool:** Title
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 5:34 - 5:40

## Visual Description

The screen clears to deliberate stillness — the 3Blue1Brown "and here's the key insight" beat. A moment of visual silence before the synthesis. The background is pure deep navy-black with only the faintest blueprint grid. A single thin horizontal line draws across the center, then the text "THE KEY INSIGHT" fades in above it, clean and authoritative.

This is a palate-cleanser between the data-heavy first half and the synthesizing conclusion. The stillness itself is the design — it creates anticipation and signals that what follows is the core takeaway.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.02 (barely visible)

### Chart/Visual Elements

#### Horizontal Rule
- Width: 300px, centered at y: 540
- Height: 1px
- Color: `#334155` at 0.4
- Draws from center outward

#### Section Label
- "THE KEY INSIGHT" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, letter-spacing 4px, centered at y: 510

#### Subtle Breathing
- The entire canvas breathes — a barely perceptible brightness oscillation (background between `#0A0F1A` and `#0B101B`)
- This creates a sense of living stillness

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Previous visual fades to black. Pure stillness. Only the faintest grid visible.
2. **Frame 40-70 (1.33-2.33s):** Horizontal rule draws from center outward. Clean, deliberate.
3. **Frame 70-110 (2.33-3.67s):** "THE KEY INSIGHT" fades in above the rule. Letter-spacing settles from 6px to 4px (slight tracking tighten).
4. **Frame 110-180 (3.67-6s):** Hold. Breathing background. Pure anticipation.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#94A3B8` at 0.5, letter-spacing 4px

### Easing
- Fade to black: `easeOut(quad)` over 30 frames
- Rule draw: `easeInOut(quad)` over 20 frames
- Text fade-in: `easeOut(quad)` over 25 frames
- Letter-spacing settle: `easeOut(cubic)` over 20 frames
- Background breathing: `easeInOut(sine)` on 90-frame cycle

## Narration Sync
> "So let me put together what I just showed you."

Segment: (transition between `part1_economics_033` and the key insight narration)

- **5:34** (silence): Screen clears to stillness
- **5:36** ("So let me put together"): Horizontal rule draws
- **5:38** ("what I just showed you"): "THE KEY INSIGHT" appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.02} />

    {/* Background breathing */}
    <BreathingBackground
      from="#0A0F1A" to="#0B101B"
      period={90} />

    {/* Horizontal rule */}
    <Sequence from={40}>
      <DrawLine from={[810, 540]} to={[1110, 540]}
        color="#334155" opacity={0.4} width={1}
        drawDuration={20} fromCenter />
    </Sequence>

    {/* Label */}
    <Sequence from={70}>
      <FadeIn duration={25}>
        <LetterSpacingSettle from={6} to={4} duration={20}>
          <Text text="THE KEY INSIGHT" font="Inter" size={14}
            weight={600} color="#94A3B8" opacity={0.5}
            letterSpacing={4} x={960} y={510} align="center" />
        </LetterSpacingSettle>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": "1.key",
  "sectionLabel": "THE KEY INSIGHT",
  "style": "stillness_beat",
  "backgroundColor": "#0A0F1A",
  "breathing": true,
  "narrationSegments": []
}
```

---
