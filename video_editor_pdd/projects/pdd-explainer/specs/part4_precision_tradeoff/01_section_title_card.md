[title:]

# Section 4.1: Part 4 Title Card — The Precision Tradeoff

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 18:30 - 18:34

## Visual Description

A clean section title card announces Part 4. "THE PRECISION" appears first in large bold weight, then "TRADEOFF" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, two abstract ghost shapes diverge — a dense coordinate grid (left, gray) representing the 3D printer's exhaustive specification, and a clean rectangular mold outline with bold wall lines (right, amber) representing injection molding's constraint-based precision.

The ghost grid has dozens of tiny dots at intersections, suggesting coordinate-by-coordinate placement. The ghost mold has only four thick wall segments, suggesting economy. The visual tension between "many points" and "few walls" foreshadows the section's argument. Background is deep navy-black with a subtle engineering-blueprint grid pattern.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05, cross-hatch pattern

### Chart/Visual Elements

#### Title Text
- "THE PRECISION" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "TRADEOFF" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 4" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- Coordinate grid: 8×8 dot matrix at (560, 480), dots `#94A3B8` at 0.03, 4px diameter, 12px spacing
  - Label: "EVERY POINT" — Inter, 8px, `#94A3B8` at 0.03, centered below
- Mold outline: rectangular with 4 thick wall segments at (1360, 480), `#D9944A` at 0.04, 3px stroke
  - Label: "WALLS ONLY" — Inter, 8px, `#D9944A` at 0.03, centered below
- Both have 8px Gaussian blur glow at respective colors, 0.02 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 4" fades in. Ghost shapes begin drawing — dots populate one by one (left), wall segments draw (right).
3. **Frame 40-60 (1.33-2s):** "THE PRECISION" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "TRADEOFF" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost shapes finish drawing. The dot grid pulses (too many) while the mold walls glow steadily (just enough).

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5
- Ghost labels: Inter, 8px, respective colors at 0.03

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "TRADEOFF" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Dot populate: stagger `easeOut(quad)`, 1 frame per dot
- Wall draw: `easeInOut(cubic)` over 40 frames
- Ghost pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."

Segment: `part4_precision_tradeoff_001`

- **0.0s** ("Let's talk about precision"): Title card begins fade-in
- **2.08s** ("because there's a subtle tradeoff"): "THE PRECISION" typing on screen
- **5.12s** ("how you think about prompts"): "TRADEOFF" revealed, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost shapes — precision paradigms foreshadowed */}
    <Sequence from={15}>
      <StaggerDots
        position={[560, 480]} rows={8} cols={8}
        dotSize={4} spacing={12} color="#94A3B8"
        opacity={0.03} staggerFrames={1}
        glow={{ blur: 8, opacity: 0.02 }}>
        <GhostLabel text="EVERY POINT" color="#94A3B8" opacity={0.03} />
      </StaggerDots>
      <StrokeDraw duration={40}>
        <MoldOutline position={[1360, 480]} color="#D9944A"
          opacity={0.04} strokeWidth={3}
          glow={{ blur: 8, opacity: 0.02 }}>
          <GhostLabel text="WALLS ONLY" color="#D9944A" opacity={0.03} />
        </MoldOutline>
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
      <DrawLine from={[860, 505]} to={[1060, 505]}
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
    { "shape": "dot_matrix", "color": "#94A3B8", "component": "coordinate_precision" },
    { "shape": "mold_outline", "color": "#D9944A", "component": "wall_precision" }
  ],
  "narrationSegments": ["part4_precision_tradeoff_001"]
}
```

---

<!-- ANNOTATION_UPDATE_START: 844c64b8-7df5-4e24-921f-7570060205f2 -->
## Annotation Update
Requested change: All required elements are present and the animation phase (Frame 260-300) is correct — all three stages visible, timeline filling, callout text shown. However, the three stage columns are clustered in the left ~65% of the canvas rather than distributed evenly across the full width. The spec places columns at approximately x: 160, 710, and 1260 (spanning the full 1920px width with even spacing). The render places them at roughly x: 120, 540, and 955, compressing them into less than two-thirds of 
Technical assessment: The three stage columns (DAY 1, MONTH 1, MONTH 6) are horizontally compressed into the left ~65% of the 1920px canvas. The spec defines column x-positions at 160, 710, and 1260 (evenly spanning the full width with ~550px spacing), but the render places them at approximately x:120, 540, and 955 (~415px spacing). This compresses the three-column layout into less than two-thirds of the frame, leaving ~900px of empty space on the right side. The timeline bar at the bottom extends further right than the columns, creating a visible misalignment. All content elements (headers, prompt documents, molds, labels, arrows, callout text) are present and correct — only the horizontal distribution is wrong. This is a Remotion layout issue with the StageColumn x-position props.
- Update the StageColumn x prop values to match the spec: Stage 1 x=160, Stage 2 x=710, Stage 3 x=1260
- Adjust the connecting arrow endpoints accordingly: Arrow 1→2 from ~(470,350) to ~(650,350), Arrow 2→3 from ~(1020,350) to ~(1200,350)
- Verify the timeline bar markers align with the updated column x-positions at 160, 710, and 1260
<!-- ANNOTATION_UPDATE_END: 844c64b8-7df5-4e24-921f-7570060205f2 -->
