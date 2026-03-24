[title:]

# Section 2.1: The Paradigm Shift — Section Title Card

**Tool:** Title
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:00 - 0:05

## Visual Description

A section title card introducing the paradigm shift argument. "THE PARADIGM" appears first in large bold weight, then "SHIFT" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of an injection mold cross-section sits at low opacity — a triangular nozzle pouring into a rectangular cavity with straight walls. The shape previews the manufacturing metaphor of the section. Background is deep navy-black, consistent with Part 1.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE PARADIGM" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "SHIFT" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 2" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (mold silhouette)
- Injection nozzle: tapered triangle pointing down, centered at (960, 380), `#4A90D9` at 0.03, 2px stroke
- Mold cavity: rectangular outline (400×200px) centered at (960, 560), `#4A90D9` at 0.03, 2px stroke
- Mold walls: two vertical lines inside cavity, `#D9944A` at 0.03, 2px stroke

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 2" label fades in. Ghost mold silhouette draws with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE PARADIGM" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "SHIFT" fades in with 10px upward slide.
6. **Frame 90-150 (3-5s):** Hold. Ghost mold silhouette pulses subtly.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "SHIFT" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost mold draw: `easeInOut(cubic)` over 30 frames
- Mold pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "So let me put together what I just showed you."

Segment: `part2_paradigm_shift_001`

- **0.00s** ("So let me put together"): Title card begins fade-in
- **1.50s** ("what I just showed you"): "THE PARADIGM" typing on screen
- **2.84s** (end of segment): "SHIFT" revealed, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost mold silhouette */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <MoldSilhouette
          nozzle={{ cx: 960, cy: 380, width: 60, height: 80 }}
          cavity={{ cx: 960, cy: 560, width: 400, height: 200 }}
          color="#4A90D9" opacity={0.03} strokeWidth={2} />
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 2" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE PARADIGM */}
    <Sequence from={40}>
      <TypeWriter text="THE PARADIGM" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[840, 505]} to={[1080, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: SHIFT */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="SHIFT" font="Inter" size={72}
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
  "sectionNumber": 2,
  "sectionLabel": "PART 2",
  "titleLine1": "THE PARADIGM",
  "titleLine2": "SHIFT",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "mold_nozzle", "color": "#4A90D9", "component": "injection_nozzle" },
    { "shape": "mold_cavity", "color": "#4A90D9", "component": "rectangular_cavity" },
    { "shape": "mold_walls", "color": "#D9944A", "component": "constraint_walls" }
  ],
  "narrationSegments": ["part2_paradigm_shift_001"]
}
```

---
