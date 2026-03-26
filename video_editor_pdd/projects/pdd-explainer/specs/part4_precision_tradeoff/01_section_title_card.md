[title:]

# Section 4.1: The Precision Tradeoff — Section Title Card

**Tool:** Title
**Duration:** ~7s (199 frames @ 30fps)
**Timestamp:** 0:00 - 0:07

## Visual Description

A section title card introducing Part 4: The Precision Tradeoff. "THE PRECISION" appears first in large bold weight, then "TRADEOFF" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of a coordinate grid with two overlaid shapes sits at very low opacity — on the left, a precise dot-matrix pattern (evoking 3D printing point-by-point placement), and on the right, a flowing filled shape hitting sharp walls (evoking injection molding). This foreshadows the core metaphor of the section.

Background is deep navy-black, consistent with the project visual language.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE PRECISION" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "TRADEOFF" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 4" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (precision motifs)
- Left ghost: dot-matrix grid pattern (5x5 dots), `#F59E0B` at 0.03, 3px circles
- Right ghost: flowing shape with sharp rectangular walls, `#2DD4BF` at 0.03, 2px stroke
- Both positioned behind title text, centered vertically

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 4" label fades in. Ghost motifs draw with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE PRECISION" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "TRADEOFF" fades in with 10px upward slide.
6. **Frame 90-160 (3-5.33s):** Hold. Ghost motifs pulse subtly.
7. **Frame 160-199 (5.33-6.63s):** Title and elements fade out, transitioning to split screen.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "TRADEOFF" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost motif draw: `easeInOut(cubic)` over 30 frames
- Motif pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 39 frames

## Narration Sync
> "Let's talk about precision, because there's a pattern here that shows up across industries. Not just cheaper materials, a deeper shift in how things are made."

Segments: `part4_precision_tradeoff_001`

- **0.00s** (seg 001): Title card begins fade-in
- **2.00s**: "THE PRECISION" typing visible
- **3.00s**: Title fully visible, hold
- **5.33s**: Begin fade-out
- **6.62s** (seg 001 ends): Fade-out complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={199}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost precision motifs */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <DotMatrixGhost color="#F59E0B" opacity={0.03} dotRadius={3}
          grid={[5, 5]} center={[760, 500]} />
      </StrokeDraw>
      <StrokeDraw duration={30}>
        <MoldFlowGhost color="#2DD4BF" opacity={0.03} strokeWidth={2}
          center={[1160, 500]} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 4" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE PRECISION */}
    <Sequence from={40}>
      <TypeWriter text="THE PRECISION" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[840, 505]} to={[1080, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: TRADEOFF */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="TRADEOFF" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Fade out */}
    <Sequence from={160}>
      <FadeOut duration={39} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 4,
  "sectionLabel": "PART 4",
  "titleLine1": "THE PRECISION",
  "titleLine2": "TRADEOFF",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "dot_matrix_grid", "color": "#F59E0B", "role": "3d_printing_precision" },
    { "shape": "mold_flow_walls", "color": "#2DD4BF", "role": "injection_molding_walls" }
  ],
  "narrationSegments": ["part4_precision_tradeoff_001"]
}
```

---
