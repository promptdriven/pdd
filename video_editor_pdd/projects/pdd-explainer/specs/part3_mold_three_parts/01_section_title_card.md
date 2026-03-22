[title:]

# Section 3.1: Part 3 Title Card — The Mold Has Three Parts

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 13:00 - 13:04

## Visual Description

A clean section title card announces Part 3. "THE MOLD HAS" appears first in large bold weight, then "THREE PARTS" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines. Behind the text, three abstract ghost shapes emerge at very low opacity — a wall segment (left, amber), an injection nozzle (center, blue), and a material texture swatch (right, green) — arranged in a triangular composition, foreshadowing the three types of capital: tests, prompts, and grounding.

Each ghost shape has a faint label beneath it — "WALLS", "NOZZLE", "MATERIAL" — barely visible, hinting at the structure to come. The background is deep navy-black with a subtle engineering-blueprint grid pattern.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05, cross-hatch pattern

### Chart/Visual Elements

#### Title Text
- "THE MOLD HAS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "THREE PARTS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 3" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Shapes (ghost elements)
- Wall segment: rectangular blocks at (560, 480), `#D9944A` at 0.04, 2px stroke
  - Label: "WALLS" — Inter, 8px, `#D9944A` at 0.03, centered below
- Injection nozzle: tapered funnel shape at (960, 430), `#4A90D9` at 0.04, 2px stroke
  - Label: "NOZZLE" — Inter, 8px, `#4A90D9` at 0.03, centered below
- Material swatch: organic flowing texture at (1360, 480), `#5AAA6E` at 0.04, 2px stroke
  - Label: "MATERIAL" — Inter, 8px, `#5AAA6E` at 0.03, centered below
- All have 8px Gaussian blur glow at respective colors, 0.02 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 3" fades in. Three ghost shapes begin drawing themselves (stroke-dashoffset animation).
3. **Frame 40-60 (1.33-2s):** "THE MOLD HAS" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "THREE PARTS" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. Ghost shapes finish drawing. Each shape pulses gently in its respective color.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5
- Ghost labels: Inter, 8px, respective colors at 0.03

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "THREE PARTS" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost shape draw: `easeInOut(cubic)` over 60 frames
- Ghost pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."

Segment: `part3_001`

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost shapes — three parts foreshadowed */}
    <Sequence from={15}>
      <StrokeDraw duration={60}>
        <WallSegment position={[560, 480]} color="#D9944A"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }}>
          <GhostLabel text="WALLS" color="#D9944A" opacity={0.03} />
        </WallSegment>
        <InjectionNozzle position={[960, 430]} color="#4A90D9"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }}>
          <GhostLabel text="NOZZLE" color="#4A90D9" opacity={0.03} />
        </InjectionNozzle>
        <MaterialSwatch position={[1360, 480]} color="#5AAA6E"
          opacity={0.04} strokeWidth={2}
          glow={{ blur: 8, opacity: 0.02 }}>
          <GhostLabel text="MATERIAL" color="#5AAA6E" opacity={0.03} />
        </MaterialSwatch>
      </StrokeDraw>
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="PART 3" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: THE MOLD HAS */}
    <Sequence from={40}>
      <TypeWriter text="THE MOLD HAS" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[860, 505]} to={[1060, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: THREE PARTS */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="THREE PARTS" font="Inter" size={72}
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
  "sectionNumber": 3,
  "sectionLabel": "PART 3",
  "titleLine1": "THE MOLD HAS",
  "titleLine2": "THREE PARTS",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "wall_segment", "color": "#D9944A", "component": "tests" },
    { "shape": "injection_nozzle", "color": "#4A90D9", "component": "prompts" },
    { "shape": "material_swatch", "color": "#5AAA6E", "component": "grounding" }
  ],
  "narrationSegments": ["part3_001"]
}
```

---

<!-- ANNOTATION_UPDATE_START: fc08f4c7-6194-4f00-8250-d490e32edd64 -->
## Annotation Update
Requested change: The frame is sampled at frame 104/120 (87.5% through the animation), which falls in the hold phase (frames 90-120). Most elements are correctly present and positioned:

**Passing elements:**
- Background: Deep navy-black background is correct.
- "PART 3": Visible above the title text with letter-spacing, correct muted color, correctly positioned.
- "THE MOLD HAS": Large bold white text, correctly rendered and centered.
- "THREE PARTS": Large bold white text, rendered below the first line.
- Ghos
Technical assessment: Frame 104/120 (87.5%, hold phase). The core title card reads correctly: deep navy-black background (#0A0F1A), 'PART 3' label with letter-spacing and muted color centered above, 'THE MOLD HAS' and 'THREE PARTS' in large bold white text centered. Three ghost shapes are faintly visible at the specified ultra-low opacities (wall segment left, nozzle center, material swatch right). Two minor spec deviations: (1) The horizontal rule between the two title lines (200px wide, 2px, #334155 at 0.5 opacity, y:505) is not visible — it should be distinguishable at 0.5 opacity even though it is thin. (2) 'THREE PARTS' appears centered rather than showing the specified 15px offset-right. Ghost labels ('WALLS', 'NOZZLE', 'MATERIAL') at 0.03 opacity and 8px size are effectively invisible, which is borderline acceptable given the extreme spec opacity. Blueprint grid at 0.05 opacity is not discernible but is acceptable at that value.
- Add or fix the horizontal rule element between 'THE MOLD HAS' and 'THREE PARTS' — it should be a 200px wide, 2px line at #334155 with 0.5 opacity centered at y:505. Verify the DrawLine component is rendering and not clipped or hidden behind text.
- Apply the 15px offset-right to 'THREE PARTS' text (x: 975 instead of 960) as specified in the Remotion code structure.
<!-- ANNOTATION_UPDATE_END: fc08f4c7-6194-4f00-8250-d490e32edd64 -->

<!-- ANNOTATION_UPDATE_START: b5ab3309-5d6c-486a-aaa5-ae2141880c47 -->
## Annotation Update
Requested change: The frame is sampled at frame 104/120 (87.5% progress) during the hold phase (frames 90-120). Most elements are correctly present: 'PART 3' section label with proper styling and positioning, 'THE MOLD HAS' and 'THREE PARTS' in large bold white text centered on canvas, dark navy-black background, and faint ghost shapes visible at low opacity on the left (wall/rectangular blocks) and right (circular/nozzle shape). However, the horizontal rule specified as 200px wide, 2px height, #334155 at 0.5 opa
Technical assessment: Frame 104/120 (87.5%, hold phase). Core title card elements are correctly rendered: deep navy-black background (#0A0F1A), 'PART 3' section label with letter-spacing and muted color at y:400, 'THE MOLD HAS' in 72px bold white at y:460, 'THREE PARTS' in 72px bold white at y:545 with 15px offset-right (code confirms calc(-50% + 15px) transform). Ghost shapes visible at ultra-low opacity on left (wall/rectangular blocks) and right (circular/nozzle). Blueprint grid at 0.05 opacity is not discernible but acceptable at that value. Ghost labels at 0.03 opacity and 8px size are effectively invisible, which is borderline acceptable given the extreme spec opacity. The primary defect is the horizontal rule (200px wide, 2px height, #334155 at 0.5 opacity, y:505) which is not visible in the rendered frame despite the code appearing correct. The rule at 2px height with a dark slate color (#334155 at 0.5 opacity ≈ #051025 effective) on the #0A0F1A background produces extremely low contrast, making it nearly invisible. The code implementation is correct per spec, but the spec's own color/opacity combination yields a practically invisible element.
- Increase the horizontal rule opacity from 0.5 to 0.7-0.8, or use a lighter color (e.g., #475569) to ensure the 200px × 2px line at y:505 is actually perceptible against the #0A0F1A background
- Alternatively, increase the rule height from 2px to 3px to improve visibility while keeping the current color and opacity
- Verify there is no z-index stacking issue where the BlueprintGrid or GhostShapes layer renders on top of the HorizontalRule — the rule is rendered after GhostShapes in the component tree so it should be on top, but confirm rendering order
<!-- ANNOTATION_UPDATE_END: b5ab3309-5d6c-486a-aaa5-ae2141880c47 -->
