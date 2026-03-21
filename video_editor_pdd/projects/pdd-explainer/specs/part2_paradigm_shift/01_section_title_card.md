[title:]

# Section 2.1: Part 2 Title Card — The Paradigm Shift

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 8:30 - 8:34

## Visual Description

A section title card announces Part 2. "THE PARADIGM" appears first in large, bold weight, then "SHIFT" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, two abstract ghost shapes emerge at very low opacity — an injection mold cross-section (left, amber) and a circuit schematic fragment (right, cool blue) — foreshadowing the manufacturing and chip-design parallels that define this section.

The background is deep navy-black with a subtle blueprint grid — faint horizontal and vertical lines evoking technical drafting paper, hinting at engineering and manufacturing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: horizontal and vertical lines at 40px spacing, `#1E293B` at 0.04; accent lines every 200px, `#1E293B` at 0.07

### Chart/Visual Elements

#### Title Text
- "THE PARADIGM" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "SHIFT" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 2" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- Injection mold cross-section: simplified mold cavity outline at (700, 480), `#D9944A` at 0.04, 2px stroke
  - Rectangular cavity with tapered nozzle at top
- Circuit schematic fragment: series of gate symbols and connecting wires at (1220, 480), `#4A90D9` at 0.04, 2px stroke
  - AND/OR gates with traces, suggesting chip design
- Both have 8px Gaussian blur glow at respective colors, 0.02 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 2" fades in. Two ghost shapes begin drawing themselves (stroke-dashoffset animation).
3. **Frame 40-60 (1.33-2s):** "THE PARADIGM" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "SHIFT" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost shapes finish drawing. The mold cavity pulses gently with a warm amber glow.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "SHIFT" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost shape draw: `easeInOut(cubic)` over 60 frames
- Mold pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "There's a pattern here that shows up across industries. Not just cheaper materials — a deeper shift in how things are made."

Segment: `part2_001`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid hSpacing={40} vSpacing={40}
      accentEvery={200} color="#1E293B"
      baseOpacity={0.04} accentOpacity={0.07} />

    {/* Ghost shapes — mold + circuit foreshadowed */}
    <Sequence from={15}>
      <StrokeDraw duration={60}>
        <MoldCavityOutline position={[700, 480]} color="#D9944A"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
        <CircuitSchematicFragment position={[1220, 480]} color="#4A90D9"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }} />
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
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[860, 505]} to={[1060, 505]}
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
    { "shape": "mold_cavity_outline", "color": "#D9944A", "component": "injection_mold" },
    { "shape": "circuit_schematic", "color": "#4A90D9", "component": "chip_design" }
  ],
  "narrationSegments": ["part2_001"]
}
```

---

<!-- ANNOTATION_UPDATE_START: c79da256-77e8-406c-a373-afb0d09abf52 -->
## Annotation Update
Requested change: The frame correctly renders the deep navy-black background with blueprint grid, the 'PART 2' section label with letter-spacing, 'THE PARADIGM' in large bold centered text, 'SHIFT' below it, and the faint ghost shapes (injection mold on left, circuit schematic on right) at very low opacity. However, the horizontal rule specified as 200px wide, 2px height, #334155 at 0.5 opacity, centered between the two title lines at y:505, is not visible in the rendered frame. This rule should have been drawn d
Technical assessment: The horizontal rule specified in the spec as 200px wide, 2px height, color #334155 at 0.5 opacity, centered at y:505 between 'THE PARADIGM' (y:460) and 'SHIFT' (y:545), is missing from the rendered frame. The spec defines this rule as drawing from center outward during frames 60-70 via a DrawLine component (from [860,505] to [1060,505]). At the current hold phase (frame 104/120), the rule should be fully drawn and visible. All other elements — background, blueprint grid, PART 2 label, both title lines, and ghost shapes — render correctly. The rule is a subtle decorative separator, but it is explicitly specified and contributes to the visual hierarchy between the two title words.
- Verify the DrawLine component is included in the Remotion composition for this scene and that it renders at the correct Sequence from={60} with drawDuration={10}
- Check that the DrawLine coordinates from=[860,505] to=[1060,505] are correct and the line is not being clipped or rendered behind another element
- Ensure the opacity value of 0.5 and color #334155 produce sufficient contrast against the #0A0F1A background — the rule should be visible though subtle
- Confirm the fromCenter draw animation completes correctly and does not leave the line at zero width after the draw duration
<!-- ANNOTATION_UPDATE_END: c79da256-77e8-406c-a373-afb0d09abf52 -->

<!-- ANNOTATION_UPDATE_START: c81a22d3-526a-43c5-be82-5da043d5a106 -->
## Annotation Update
Requested change: The frame is at 90.5% progress (frame 379/420), corresponding to the final hold phase where perfect parts should be visible with green checkmarks and the mold pulses with amber glow. Several critical and major issues are visible: (1) The background uses a photographic factory floor image instead of the specified #0A0F1A deep navy-black with faint 40px drafting grid — this is a fundamental departure from the clean vector/engineering-diagram aesthetic. (2) The ejected parts below the mold appear a
Technical assessment: Frame 379/420 is in the final hold phase (frames 340-420) of the Remotion-animated 'Defect → Fix the Mold' sequence. The background correctly uses the #0A0F1A deep navy-black (the annotation's claim of a photographic factory floor appears to be incorrect — the rendered frame shows the correct dark background). The mold diagram, ejected parts with green checkmarks, 'Fix the mold' label, and 'All future parts: fixed' counter are all present and correctly positioned. However, two issues are visible: (1) The 'Defect detected' label and associated red circles/indicators are still visible at frame 379 — per the spec, the defective part should have dissolved at frames 280-310 via ParticleDissolve, and the defect callout should no longer be rendered. This creates visual confusion by showing both 'Defect detected' and 'All future parts: fixed' simultaneously. (2) The mold is not visibly pulsing with the 'satisfied amber glow' specified for the hold phase (frames 340-420). The drafting grid at 40px/0.04 opacity is extremely subtle but may be present. The ejected parts appear correctly sized and positioned with green checkmarks, matching the spec's #5AAA6E overlay.
- Ensure the DefectPulse component, magnifying glass icon, and 'Defect detected' label are bounded within a Sequence that ends before the hold phase — they should not persist past frame 280 when the defective part dissolves
- Add an amber glow pulse animation to the mold during the hold phase (frames 340-420) using easeInOut(sine) opacity oscillation on the wall fill between #D9944A at 0.3 and 0.6
- Verify the ParticleDissolve at frame 280 fully removes the defective part and its associated callout elements
- Confirm the DraftGrid component renders at 40px spacing with #1E293B at 0.04 opacity — increase opacity slightly to 0.06 if completely invisible
<!-- ANNOTATION_UPDATE_END: c81a22d3-526a-43c5-be82-5da043d5a106 -->
