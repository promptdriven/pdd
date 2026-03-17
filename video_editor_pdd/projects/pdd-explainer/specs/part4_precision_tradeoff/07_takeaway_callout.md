[title:]

# Section 4.7: Takeaway Callout — More Tests, Less Prompt

**Tool:** Title
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 19:38 - 19:46

## Visual Description

A full-screen emphasized callout that drives home the core insight of Part 4. The screen darkens to near-black, then the text appears in two beats:

First beat: "More tests, less prompt." — large, bold, centered. The word "tests" glows amber (the wall color), and "prompt" glows blue (the specification color). A visual echo of the inverse curve appears as a faint ghost behind the text — the hyperbola from the previous chart, barely visible, reinforcing the mathematical relationship.

Second beat: "The walls do the precision work." — appears below, slightly smaller, in warm amber. The word "walls" pulses gently with the same glow used on the mold walls throughout Part 4.

Below the text, a minimal bar graphic shows 4 amber blocks (walls/tests) on the left equaling a single condensed blue block (prompt) on the right, with an equals sign between them. Visual shorthand: 4 constraints = 1 simple prompt.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#060A14` (near-black)
- Ghost curve: the inverse hyperbola from 05_precision_tradeoff_curve, `#E2E8F0` at 0.03, 2px, positioned behind text

### Chart/Visual Elements

#### Primary Text
- "More tests, less prompt." — Inter, 52px, bold (700), `#E2E8F0`, centered at y: 420
  - "tests" highlighted: `#D9944A` at 1.0, with 12px glow at `#D9944A` 0.15
  - "prompt" highlighted: `#4A90D9` at 1.0, with 12px glow at `#4A90D9` 0.15
  - Remaining words: `#E2E8F0` at 0.8

#### Secondary Text
- "The walls do the precision work." — Inter, 32px, semi-bold (600), `#D9944A` at 0.7, centered at y: 510
  - "walls" has pulsing glow: `#D9944A` at 0.2, 15px blur, `easeInOut(sine)` cycle

#### Bar Equivalence Graphic
- Positioned at y: 640, centered
- LEFT: 4 amber blocks in a row, each 40x30px, `#D9944A` at 0.5, 4px gap between
  - Tiny labels below each: "T1", "T2", "T3", "T4" — JetBrains Mono, 8px, `#D9944A` at 0.3
- CENTER: "=" sign — Inter, 28px, `#64748B` at 0.4, at x: 960
- RIGHT: 1 blue block, 40x30px, `#4A90D9` at 0.5
  - Tiny label below: "prompt" — JetBrains Mono, 8px, `#4A90D9` at 0.3

#### Ghost Curve (background)
- Same data points as 05_precision_tradeoff_curve
- Very faint: `#E2E8F0` at 0.03, 2px stroke
- Positioned to fill background behind text, scaled to ~800x400px centered

### Animation Sequence
1. **Frame 0-30 (0-1s):** Screen darkens from previous scene to `#060A14`. Ghost curve fades in at 0.03 opacity.
2. **Frame 30-80 (1-2.67s):** "More tests, less prompt." types on word-by-word. "tests" glows amber as it appears. "prompt" glows blue. Period punctuates with a subtle flash.
3. **Frame 80-130 (2.67-4.33s):** "The walls do the precision work." fades in below with a 10px upward slide. "walls" begins pulsing.
4. **Frame 130-180 (4.33-6s):** Bar equivalence graphic draws in — 4 amber blocks appear one-by-one from left, then equals sign, then blue block.
5. **Frame 180-240 (6-8s):** Hold. All elements visible. "walls" continues pulsing. Ghost curve breathes. The insight lands.

### Typography
- Primary text: Inter, 52px, bold (700), `#E2E8F0` at 0.8 (with highlighted words)
- Secondary text: Inter, 32px, semi-bold (600), `#D9944A` at 0.7
- Block labels: JetBrains Mono, 8px, respective colors at 0.3
- Equals sign: Inter, 28px, `#64748B` at 0.4

### Easing
- Screen darken: `easeInOut(quad)` over 30 frames
- Word-by-word type: `easeOut(quad)` per word, 10 frames gap
- Word glow: `easeOut(cubic)` over 10 frames
- Secondary text slide-up: `easeOut(cubic)` over 20 frames
- "walls" pulse: `easeInOut(sine)` on 40-frame cycle
- Block appearance: `easeOut(back(1.3))` scale bounce, 8 frames each, 6 frame stagger
- Ghost curve fade: `easeOut(quad)` over 30 frames

## Narration Sync
> "This is why test accumulation matters. It's not just about catching bugs. It's about making prompts simpler and regeneration safer over time."
> "The more walls you have, the less you need to specify. The mold does the precision work."

Segment: `part4_007`

- **19:38** ("test accumulation matters"): Screen darkens, ghost curve appears
- **19:40** ("not just about catching bugs"): Primary text appearing
- **19:43** ("making prompts simpler"): "More tests, less prompt." fully visible
- **19:46** ("The mold does the precision work"): Secondary text and bar graphic visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#060A14' }}>
    {/* Ghost curve background */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <GhostCurve data={precisionTradeoffData}
          color="#E2E8F0" opacity={0.03} width={2}
          center={[960, 450]} size={[800, 400]} />
      </FadeIn>
    </Sequence>

    {/* Primary text — word by word */}
    <Sequence from={30}>
      <WordByWord text="More tests, less prompt."
        font="Inter" size={52} weight={700}
        baseColor="#E2E8F0" baseOpacity={0.8}
        y={420} align="center"
        wordDelay={10}
        highlights={[
          { word: "tests", color: "#D9944A", glow: { radius: 12, opacity: 0.15 } },
          { word: "prompt.", color: "#4A90D9", glow: { radius: 12, opacity: 0.15 } }
        ]} />
    </Sequence>

    {/* Secondary text */}
    <Sequence from={80}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <PulsingText text="The walls do the precision work."
            font="Inter" size={32} weight={600}
            color="#D9944A" opacity={0.7}
            x={960} y={510} align="center"
            pulseWord="walls"
            pulseGlow={{ radius: 15, opacity: 0.2, period: 40 }} />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Bar equivalence graphic */}
    <Sequence from={130}>
      <BarEquivalence y={640}
        leftBlocks={4} leftColor="#D9944A" leftOpacity={0.5}
        leftLabels={["T1", "T2", "T3", "T4"]}
        rightBlocks={1} rightColor="#4A90D9" rightOpacity={0.5}
        rightLabels={["prompt"]}
        blockSize={[40, 30]} gap={4}
        equalsColor="#64748B"
        stagger={6} bounceScale={1.3} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "callout_card",
  "calloutId": "more_tests_less_prompt",
  "primaryText": "More tests, less prompt.",
  "secondaryText": "The walls do the precision work.",
  "highlights": [
    { "word": "tests", "color": "#D9944A", "meaning": "test constraints / mold walls" },
    { "word": "prompt", "color": "#4A90D9", "meaning": "specification / prompt detail" }
  ],
  "barEquivalence": {
    "left": { "count": 4, "label": "tests", "color": "#D9944A" },
    "right": { "count": 1, "label": "prompt", "color": "#4A90D9" }
  },
  "ghostBackground": "precision_tradeoff_curve",
  "backgroundColor": "#060A14",
  "narrationSegments": ["part4_007"]
}
```

---
