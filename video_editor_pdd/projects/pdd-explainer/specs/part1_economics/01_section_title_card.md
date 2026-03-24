[title:]

# Section 1.1: The Economics of Darning — Section Title Card

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:00 - 0:04

## Visual Description

A section title card introducing the economic argument. "THE ECONOMICS" appears first in large bold weight, then "OF DARNING" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost image of intersecting cost curves — one descending, one ascending — sits at low opacity, previewing the charting theme of the section. The curves cross near center-right, hinting at the threshold moment. Background is deep navy-black.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE ECONOMICS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "OF DARNING" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 1" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (cost curves)
- Two quadratic bezier curves, crossing at (1050, 500)
- Descending curve: `#D9944A` at 0.04, 2px stroke
- Ascending curve: `#4A90D9` at 0.04, 2px stroke
- Crossing point: small circle 8px, `#E2E8F0` at 0.05

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 1" label fades in. Ghost cost curves draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE ECONOMICS" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "OF DARNING" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost curves pulse subtly.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "OF DARNING" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost curve draw: `easeInOut(cubic)` over 30 frames
- Curve pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Watch this."
> "15 lines of prompt. 200 lines of code."

Segment: `part1_economics_001`, `part1_economics_002`

- **0.00s** ("Watch this."): Title card begins fade-in
- **0.74s** ("15 lines of prompt"): "THE ECONOMICS" typing on screen
- **2.5s** ("200 lines of code"): "OF DARNING" revealed, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost cost curves */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <QuadraticCurve
          points={[[200, 300], [600, 480], [1050, 500]]}
          color="#D9944A" opacity={0.04} width={2} />
        <QuadraticCurve
          points={[[200, 700], [600, 520], [1050, 500]]}
          color="#4A90D9" opacity={0.04} width={2} />
        <Circle cx={1050} cy={500} r={4}
          fill="#E2E8F0" opacity={0.05} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 1" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE ECONOMICS */}
    <Sequence from={40}>
      <TypeWriter text="THE ECONOMICS" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[840, 505]} to={[1080, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: OF DARNING */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="OF DARNING" font="Inter" size={72}
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
  "sectionNumber": 1,
  "sectionLabel": "PART 1",
  "titleLine1": "THE ECONOMICS",
  "titleLine2": "OF DARNING",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "quadratic_curve", "color": "#D9944A", "component": "descending_cost" },
    { "shape": "quadratic_curve", "color": "#4A90D9", "component": "ascending_cost" },
    { "shape": "crossing_point", "color": "#E2E8F0", "component": "threshold" }
  ],
  "narrationSegments": ["part1_economics_001", "part1_economics_002"]
}
```

---
