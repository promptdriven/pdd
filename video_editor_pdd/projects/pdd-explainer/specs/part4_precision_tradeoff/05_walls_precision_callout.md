[Remotion]

# Section 4.5: "More Walls, Less Prompt" — Animated Insight Callout

**Tool:** Remotion
**Duration:** ~6s (186 frames @ 30fps)
**Timestamp:** 0:58 - 1:04

## Visual Description

A kinetic typography moment that drives home the section's core insight. The screen is clean — dark background with the inverse curve from spec 03 faintly visible as a ghost reference in the background.

The text "More tests, less prompt." appears word by word in large bold type, center-screen. As each word lands, a visual reinforcement plays:

- "More" — test wall icons multiply on the left, stacking up.
- "tests," — walls glow teal.
- "less" — a prompt document visually shrinks (from 50 lines to 10 lines).
- "prompt." — the small prompt pulses with a checkmark.

Below, a secondary line fades in: "The walls do the precision work." — quieter, smaller, the explanatory anchor.

The entire composition breathes confidence and clarity — this is the "remember this" moment of the section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Ghost curve: from spec 03, `#A78BFA` at 0.03, 1px stroke (barely visible)

### Chart/Visual Elements

#### Primary Text
- "More tests," — Inter, 64px, bold (700), `#2DD4BF`, centered at y: 440
- "less prompt." — Inter, 64px, bold (700), `#F59E0B`, centered at y: 530
- Emphasis: "More" and "less" have slight letter-spacing 2px for weight

#### Secondary Text
- "The walls do the precision work." — Inter, 20px, normal (400), `#94A3B8` at 0.6, centered at y: 640

#### Test Wall Icons (left of center)
- 8 rectangular wall segments, stacked vertically
- Each: 4px × 30px, `#2DD4BF` at 0.5
- Positioned at x: 340, fanning from y: 400 to y: 570
- Appear one by one with stagger

#### Prompt Document Icon (right of center)
- Starts as tall document: 60×100px with 12 text lines, `#F59E0B` at 0.3
- Shrinks to: 60×40px with 3 text lines, `#F59E0B` at 0.3
- Checkmark appears on top: `#22C55E`, 16px

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Ghost curve fades in. Clean stage set.
2. **Frame 20-50 (0.67-1.67s):** "More" appears with slide-up. Test walls begin stacking (1 every 4 frames).
3. **Frame 50-80 (1.67-2.67s):** "tests," appears. Walls glow — `#2DD4BF` pulses. 8 walls visible.
4. **Frame 80-110 (2.67-3.67s):** "less" appears. Prompt document begins shrinking animation.
5. **Frame 110-140 (3.67-4.67s):** "prompt." appears. Prompt is small, checkmark lands on it.
6. **Frame 140-160 (4.67-5.33s):** Secondary line fades in: "The walls do the precision work."
7. **Frame 160-186 (5.33-6.2s):** Hold. Everything visible. Clean, confident composition.

### Typography
- Primary text: Inter, 64px, bold (700), respective colors
- Secondary text: Inter, 20px, normal (400), `#94A3B8` at 0.6

### Easing
- Word appear: `easeOut(back)` over 15 frames — slight overshoot for impact
- Wall stack: `easeOut(quad)` per wall, 4-frame stagger
- Wall glow pulse: `easeInOut(sine)` over 20 frames
- Document shrink: `easeInOut(cubic)` over 30 frames
- Checkmark: `spring(damping: 10)` over 15 frames
- Secondary text: `easeOut(quad)` over 20 frames

## Narration Sync
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segments: `part4_precision_tradeoff_008`

- **58.24s** (seg 008): "More" appears, walls begin stacking
- **60s**: "tests, less" — document shrinking
- **62s**: "prompt." — checkmark, secondary line
- **64.46s** (seg 008 ends): Hold, composition complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={186}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Ghost curve reference */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <GhostCurve fn={(x) => 200 + 600 * Math.exp(-0.04 * x)}
          color="#A78BFA" opacity={0.03} strokeWidth={1} />
      </FadeIn>
    </Sequence>

    {/* Test wall icons */}
    <Sequence from={20}>
      <StaggeredStack count={8} stagger={4}
        x={340} yStart={400} yEnd={570}
        itemWidth={4} itemHeight={30}
        color="#2DD4BF" opacity={0.5}>
        <Sequence from={30}>
          <GlowPulse color="#2DD4BF" duration={20} />
        </Sequence>
      </StaggeredStack>
    </Sequence>

    {/* Prompt document icon */}
    <Sequence from={20}>
      <PromptDocument x={1560} y={430}
        initialWidth={60} initialHeight={100} initialLines={12}
        finalWidth={60} finalHeight={40} finalLines={3}
        color="#F59E0B" opacity={0.3}
        shrinkStartFrame={60} shrinkDuration={30} />
      <Sequence from={90}>
        <Checkmark x={1590} y={420} size={16} color="#22C55E" />
      </Sequence>
    </Sequence>

    {/* Primary text — word by word */}
    <Sequence from={20}>
      <SlideUp distance={15} duration={15}>
        <Text text="More" font="Inter" size={64} weight={700}
          color="#2DD4BF" letterSpacing={2} x={700} y={440} />
      </SlideUp>
    </Sequence>
    <Sequence from={50}>
      <SlideUp distance={15} duration={15}>
        <Text text="tests," font="Inter" size={64} weight={700}
          color="#2DD4BF" x={880} y={440} />
      </SlideUp>
    </Sequence>
    <Sequence from={80}>
      <SlideUp distance={15} duration={15}>
        <Text text="less" font="Inter" size={64} weight={700}
          color="#F59E0B" letterSpacing={2} x={750} y={530} />
      </SlideUp>
    </Sequence>
    <Sequence from={110}>
      <SlideUp distance={15} duration={15}>
        <Text text="prompt." font="Inter" size={64} weight={700}
          color="#F59E0B" x={920} y={530} />
      </SlideUp>
    </Sequence>

    {/* Secondary text */}
    <Sequence from={140}>
      <FadeIn duration={20}>
        <Text text="The walls do the precision work."
          font="Inter" size={20} weight={400}
          color="#94A3B8" opacity={0.6}
          x={960} y={640} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "kinetic_typography",
  "primaryText": ["More tests,", "less prompt."],
  "secondaryText": "The walls do the precision work.",
  "visualElements": {
    "testWalls": { "count": 8, "color": "#2DD4BF" },
    "promptDocument": { "initialLines": 12, "finalLines": 3, "color": "#F59E0B" },
    "checkmark": { "color": "#22C55E" }
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_008"]
}
```

---
