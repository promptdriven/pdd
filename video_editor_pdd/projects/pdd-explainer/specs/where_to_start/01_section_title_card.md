[title:]

# Section 6.1: Where to Start — Section Title Card

**Tool:** Title
**Duration:** ~18s (546 frames @ 30fps)
**Timestamp:** 0:00 - 0:18

## Visual Description

A section title card introducing the "Where to Start" segment. "WHERE TO" appears in large bold weight, then "START" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of a codebase outline sits at very low opacity — a grid of small rectangles representing modules, with one rectangle glowing slightly brighter than the rest. This foreshadows the "start with one module" thesis. Background is deep navy-black consistent with the overall visual language.

The title holds across the first narration segment covering the acknowledgement that nobody works on greenfield projects and the introduction of PDD's ability to create prompts from existing code. The card fades out as the narration pivots to the `pdd update` terminal command.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "WHERE TO" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "START" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 280px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "WHERE TO START" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (module grid)
- 6x4 grid of small rectangles (40x25px each), `#1E293B` at 0.06, 20px gap
- One rectangle (row 2, col 3) slightly brighter: `#5AAA6E` at 0.08
- Subtle radial glow around bright rectangle: `#5AAA6E` at 0.03, 40px radius

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** Section label fades in. Ghost module grid draws rectangle by rectangle.
3. **Frame 40-60 (1.33-2s):** "WHERE TO" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "START" fades in with 10px upward slide.
6. **Frame 90-486 (3-16.2s):** Hold. One module in ghost grid pulses subtly. Title stays visible through opening narration.
7. **Frame 486-546 (16.2-18.2s):** Title and elements fade out, transitioning to legacy codebase reveal.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "START" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost grid draw: `easeInOut(cubic)` over 30 frames, staggered 2 frames per rectangle
- Module pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "PDD can create prompts from existing code. Start with one module. Generate its prompt. Add tests. Regenerate. Compare. When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001`

- **0.00s** (seg 001): Title card begins fade-in
- **2.00s**: "WHERE TO" typing visible
- **3.00s**: Title fully visible, hold during opening narration
- **18.20s** (seg 001 ends): Title begins fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={546}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost module grid */}
    <Sequence from={15}>
      <StaggeredReveal delay={2} duration={30}>
        <ModuleGrid
          rows={4} cols={6}
          cellSize={{ w: 40, h: 25 }}
          gap={20}
          color="#1E293B" opacity={0.06}
          highlight={{ row: 2, col: 3, color: "#5AAA6E", opacity: 0.08 }}
        />
      </StaggeredReveal>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="WHERE TO START" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: WHERE TO */}
    <Sequence from={40}>
      <TypeWriter text="WHERE TO" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[820, 505]} to={[1100, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: START */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="START" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Fade out */}
    <Sequence from={486}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 6,
  "sectionLabel": "WHERE TO START",
  "titleLine1": "WHERE TO",
  "titleLine2": "START",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "module_grid", "rows": 4, "cols": 6, "highlightCell": [2, 3], "role": "one_module_preview" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
