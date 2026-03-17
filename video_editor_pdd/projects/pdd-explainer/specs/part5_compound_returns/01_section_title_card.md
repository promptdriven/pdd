[title:]

# Section 5.1: Part 5 Title Card — Compound Returns

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 21:00 - 21:04

## Visual Description

A clean section title card announces Part 5. "COMPOUND" appears first in large, bold weight, then "RETURNS" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, two abstract ghost curves diverge from a shared origin — an amber curve (#D9944A) sweeping exponentially upward (debt) and a blue curve (#4A90D9) staying flat then gently declining (PDD) — foreshadowing the section's central divergence argument.

The background is deep navy-black with a subtle ledger-paper grid — faint horizontal lines with slightly brighter vertical accents, continuing the economic visual language from Part 1.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Ledger grid: horizontal lines at 40px spacing, `#1E293B` at 0.04; vertical accents every 120px, `#1E293B` at 0.06

### Chart/Visual Elements

#### Title Text
- "COMPOUND" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "RETURNS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 5" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- Diverging curves from shared origin at (960, 520):
  - Amber curve: exponential rise to upper-right (1300, 350), `#D9944A` at 0.04, 2px stroke
  - Blue curve: flat trajectory to lower-right (1300, 550), `#4A90D9` at 0.04, 2px stroke
- Both have 8px Gaussian blur glow at respective colors, 0.02 opacity
- Shared origin point: small circle, `#E2E8F0` at 0.03

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Ledger grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 5" fades in. Ghost curves begin drawing from shared origin (stroke-dashoffset animation), diverging outward.
3. **Frame 40-60 (1.33-2s):** "COMPOUND" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "RETURNS" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost curves finish drawing. The divergence gap between them pulses gently.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "RETURNS" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost curve draw: `easeInOut(cubic)` over 60 frames
- Divergence pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Now let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."

Segment: `part5_001`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <LedgerGrid hSpacing={40} vAccentEvery={120}
      color="#1E293B" hOpacity={0.04} vOpacity={0.06} />

    {/* Ghost shapes — diverging curves foreshadowed */}
    <Sequence from={15}>
      <StrokeDraw duration={60}>
        <DivergingCurves
          origin={[960, 520]}
          amberEnd={[1300, 350]} blueEnd={[1300, 550]}
          amberColor="#D9944A" blueColor="#4A90D9"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 5" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: COMPOUND */}
    <Sequence from={40}>
      <TypeWriter text="COMPOUND" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[860, 505]} to={[1060, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: RETURNS */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="RETURNS" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 5,
  "sectionLabel": "PART 5",
  "titleLine1": "COMPOUND",
  "titleLine2": "RETURNS",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "exponential_curve", "color": "#D9944A", "component": "debt_growth" },
    { "shape": "flat_curve", "color": "#4A90D9", "component": "pdd_flat" }
  ],
  "narrationSegments": ["part5_001"]
}
```

---
