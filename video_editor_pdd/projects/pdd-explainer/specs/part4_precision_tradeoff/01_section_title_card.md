[title:]

# Section 4.1: Part 4 Title Card — The Precision Tradeoff

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 18:30 - 18:34

## Visual Description

A section title card introduces Part 4. "THE PRECISION" appears first in large bold weight, then "TRADEOFF" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, two ghost shapes emerge at very low opacity — a 3D printer nozzle tracing a coordinate grid (left, cool blue) and an injection mold cross-section with flowing material (right, warm amber) — foreshadowing the core metaphor of this section: precise specification versus constraint-based precision.

The background is deep navy-black with a subtle graph-paper grid — faint lines evoking mathematical precision, suggesting that this section deals with measurable tradeoffs.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Graph-paper grid: horizontal and vertical lines at 40px spacing, `#1E293B` at 0.04; accent lines every 200px, `#1E293B` at 0.07

### Chart/Visual Elements

#### Title Text
- "THE PRECISION" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "TRADEOFF" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 220px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 4" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- 3D printer nozzle + coordinate grid: simplified nozzle icon with dotted grid traces at (700, 480), `#4A90D9` at 0.04, 2px stroke
  - Nozzle pointing downward with small grid of dot-points below, suggesting point-by-point placement
- Injection mold with flow: simplified mold cavity with wavy flow lines inside at (1220, 480), `#D9944A` at 0.04, 2px stroke
  - Rectangular cavity with flowing liquid shapes, suggesting material constrained by walls
- Both have 8px Gaussian blur glow at respective colors, 0.02 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Graph-paper grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 4" fades in. Two ghost shapes begin drawing themselves (stroke-dashoffset animation).
3. **Frame 40-60 (1.33-2s):** "THE PRECISION" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "TRADEOFF" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost shapes finish drawing. The mold flow lines pulse gently with warm amber glow.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "TRADEOFF" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost shape draw: `easeInOut(cubic)` over 60 frames
- Flow pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."

Segment: `part4_001`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <GraphPaperGrid hSpacing={40} vSpacing={40}
      accentEvery={200} color="#1E293B"
      baseOpacity={0.04} accentOpacity={0.07} />

    {/* Ghost shapes — printer + mold foreshadowed */}
    <Sequence from={15}>
      <StrokeDraw duration={60}>
        <PrinterNozzleGrid position={[700, 480]} color="#4A90D9"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
        <MoldFlowOutline position={[1220, 480]} color="#D9944A"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
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
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[850, 505]} to={[1070, 505]}
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
    { "shape": "printer_nozzle_grid", "color": "#4A90D9", "component": "3d_printer" },
    { "shape": "mold_flow_outline", "color": "#D9944A", "component": "injection_mold" }
  ],
  "narrationSegments": ["part4_001"]
}
```

---
