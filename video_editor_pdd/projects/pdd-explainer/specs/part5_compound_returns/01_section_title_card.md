[title:]

# Section 5.1: Compound Returns — Section Title Card

**Tool:** Title
**Duration:** ~27s (812 frames @ 30fps)
**Timestamp:** 0:00 - 0:27

## Visual Description

A section title card introducing Part 5. "COMPOUND" appears in large bold weight, then "RETURNS" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of two diverging exponential curves sits at very low opacity — one curving up (debt compounding against you), one staying flat (regeneration resets). This foreshadows the core thesis of the section. Background is deep navy-black consistent with the overall visual language.

The title holds across the first narration segment covering the zoom-out transition ("Now, let's zoom out. Because the numbers you just saw...") through the maintenance statistics (McKinsey, Stripe data). The card fades out as the narration pivots to the compound interest curve visual.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "COMPOUND" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "RETURNS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 280px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 5" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (diverging curves)
- Upward exponential curve: `#D9944A` at 0.04, 1.5px stroke — arcs from bottom-left to top-right
- Flat horizontal line: `#5AAA6E` at 0.04, 1.5px stroke — stays level across the canvas
- Gap between them: subtle radial glow at divergence point, `#FFFFFF` at 0.02, 25px radius

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 5" label fades in. Ghost diverging curves draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "COMPOUND" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "RETURNS" fades in with 10px upward slide.
6. **Frame 90-750 (3-25s):** Hold. Ghost curves pulse subtly. Title stays visible through maintenance stats narration.
7. **Frame 750-812 (25-27s):** Title and elements fade out, transitioning to pie chart.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "RETURNS" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost curves draw: `easeInOut(cubic)` over 30 frames
- Curves pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 62 frames

## Narration Sync
> "Now, let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it. McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

Segment: `part5_compound_returns_001`

- **0.00s** (seg 001): Title card begins fade-in
- **2.00s**: "COMPOUND" typing visible
- **3.00s**: Title fully visible, hold during maintenance stats narration
- **27.08s** (seg 001 ends): Title begins fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={812}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost diverging curves */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <DivergingCurves
          upCurve={{ color: "#D9944A", opacity: 0.04 }}
          flatLine={{ color: "#5AAA6E", opacity: 0.04 }}
          strokeWidth={1.5}
        />
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
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[820, 505]} to={[1100, 505]}
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

    {/* Fade out */}
    <Sequence from={750}>
      <FadeOut duration={62} />
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
    { "shape": "diverging_curves", "colors": ["#D9944A", "#5AAA6E"], "role": "compound_cost_preview" }
  ],
  "narrationSegments": ["part5_compound_returns_001"]
}
```

---
