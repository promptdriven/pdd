[title:]

# Section 6.1: Where to Start — Section Title Card

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:00 - 0:04

## Visual Description

A section title card introducing the practical adoption section. "WHERE TO" appears first in large bold weight, then "START" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of a codebase grid pattern — small rectangular blocks arranged in a staggered layout like file/module icons. One block near the center glows faintly blue — previewing the "start with one module" theme. The rest remain dim gray. Background is deep navy-black.

The title holds briefly to orient the viewer, then transitions into the legacy codebase reveal.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "WHERE TO" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "START" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 180px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 6" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (module grid)
- 6x4 grid of small rounded rectangles: 30x20px, `#475569` at 0.04
- Center block: `#4A90D9` at 0.08, soft glow 10px
- Grid centered at (960, 540), spacing 80px horizontal, 50px vertical

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Background fades in from black. Blueprint grid appears.
2. **Frame 10-25 (0.33-0.83s):** "PART 6" label fades in. Ghost module grid fades in.
3. **Frame 25-45 (0.83-1.5s):** "WHERE TO" types on character-by-character (2 frames per character).
4. **Frame 45-55 (1.5-1.83s):** Horizontal rule draws from center outward.
5. **Frame 55-70 (1.83-2.33s):** "START" fades in with 10px upward slide.
6. **Frame 70-100 (2.33-3.33s):** Hold. Center ghost block pulses gently.
7. **Frame 100-120 (3.33-4s):** Title begins fade-out, transitioning to legacy codebase.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 15 frames
- "START" slide-up: `easeOut(cubic)` over 15 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost grid fade-in: `easeOut(quad)` over 20 frames
- Center block pulse: `easeInOut(sine)` on 45-frame cycle
- Title fade-out: `easeIn(quad)` over 20 frames

## Narration Sync
> (No narration — visual title card overlaps with the opening beat of segment where_to_start_001)

Segment: `where_to_start_001` (opening)

- **0:00** (0.00s): Title card begins fade-in
- **0:02** (2.00s): Title fully visible, hold
- **0:04** (4.00s): Title fading out, transitioning to legacy codebase

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost module grid */}
    <Sequence from={10}>
      <FadeIn duration={20}>
        <ModuleGrid
          rows={4} cols={6} cellSize={[30, 20]}
          spacingX={80} spacingY={50}
          center={[960, 540]}
          color="#475569" opacity={0.04}
          highlightIndex={13} highlightColor="#4A90D9"
          highlightOpacity={0.08} glowRadius={10}
          pulseCycle={45}
        />
      </FadeIn>
    </Sequence>

    {/* Section label */}
    <Sequence from={10}>
      <FadeIn duration={15}>
        <Text text="PART 6" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: WHERE TO */}
    <Sequence from={25}>
      <TypeWriter text="WHERE TO" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={45}>
      <DrawLine from={[870, 505]} to={[1050, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: START */}
    <Sequence from={55}>
      <SlideUp distance={10} duration={15}>
        <FadeIn duration={15}>
          <Text text="START" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>

    {/* Fade out */}
    <Sequence from={100}>
      <FadeOut duration={20}>
        <AbsoluteFill />
      </FadeOut>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 6,
  "sectionLabel": "PART 6",
  "titleLine1": "WHERE TO",
  "titleLine2": "START",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "module_grid", "rows": 4, "cols": 6, "highlightIndex": 13, "highlightColor": "#4A90D9" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
