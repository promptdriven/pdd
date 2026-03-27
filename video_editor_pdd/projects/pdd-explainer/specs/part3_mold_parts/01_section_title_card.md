[title:]

# Section 3.1: The Mold Has Three Parts — Section Title Card

**Tool:** Title
**Duration:** ~44s (1320 frames @ 30fps)
**Timestamp:** 0:00 - 0:43

## Visual Description

A section title card introducing Part 3. "THE MOLD HAS" appears in large bold weight, then "THREE PARTS" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of an injection mold cross-section sits at very low opacity — three regions (walls, nozzle, cavity) barely visible, foreshadowing the three-part thesis. Background is deep navy-black consistent with the overall visual language.

The title holds across five narration segments covering the "same wall" callback to chips, the transition to PDD, the "prompt is your mold" thesis, and the "now let's get precise" pivot. The card fades out as the narration moves to the detailed three-component breakdown.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE MOLD HAS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "THREE PARTS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 280px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 3" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (mold cross-section)
- Three outlined regions representing walls, nozzle, and cavity
- Stroke: `#4A90D9` at 0.04, 1.5px
- Walls region pulses subtly every 60 frames
- Nozzle region: `#D9944A` at 0.03
- Cavity: `#4AD9A0` at 0.03

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 3" label fades in. Ghost mold outline begins drawing with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE MOLD HAS" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "THREE PARTS" fades in with 10px upward slide.
6. **Frame 90-1260 (3-42s):** Hold. Ghost mold regions pulse subtly in sequence. Title stays visible through introductory narration covering the chip-industry callback, the mold metaphor, and the "now let's get precise" pivot.
7. **Frame 1260-1320 (42-44s):** Title and elements fade out, transitioning to mold cross-section.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "THREE PARTS" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost mold draw: `easeInOut(cubic)` over 30 frames
- Region pulse: `easeInOut(sine)` on 60-frame cycle
- Final fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "We're hitting the same wall with AI-generated code. When AI generates ten thousand lines in a day, code review becomes netlist review. The question isn't whether you should review it. It's whether you can."
> "The chip industry's answer wasn't 'review harder.' It was: verify the output against the spec. Review the Verilog, not the gates. That's what tests do for generated code."
> "This is that same transition. For software."
> "The prompt is your mold. The code is just plastic. And just like chip synthesis — the code is different every generation. But the tests lock the behavior. The process is deterministic."
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete. In PDD, the mold has three components. Three types of capital you're accumulating."

Segments: `part3_mold_parts_001`, `part3_mold_parts_002`, `part3_mold_parts_003`, `part3_mold_parts_004`, `part3_mold_parts_005`

- **0.00s** (seg 001): Title card begins fade-in
- **12.94s** (seg 001 ends): Title fully visible, hold
- **13.52s** (seg 002): Chip industry callback narration
- **26.58s** (seg 002 ends): Hold
- **26.76s** (seg 003): "This is that same transition"
- **30.14s** (seg 003 ends): Hold
- **30.46s** (seg 004): "The prompt is your mold"
- **43.52s** (seg 004 ends): Hold
- **43.92s** (seg 005): "Now let's get precise" — title begins fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1320}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost mold cross-section */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <MoldOutline
          walls={{ color: "#4A90D9", opacity: 0.04 }}
          nozzle={{ color: "#D9944A", opacity: 0.03 }}
          cavity={{ color: "#4AD9A0", opacity: 0.03 }}
          strokeWidth={1.5}
        />
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
        charDelay={2} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[820, 505]} to={[1100, 505]}
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

    {/* Fade out */}
    <Sequence from={1260}>
      <FadeOut duration={60} />
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
    { "shape": "mold_cross_section", "regions": ["walls", "nozzle", "cavity"], "role": "three_parts_preview" }
  ],
  "narrationSegments": ["part3_mold_parts_001", "part3_mold_parts_002", "part3_mold_parts_003", "part3_mold_parts_004", "part3_mold_parts_005"],
  "durationSeconds": 44.0
}
```

---
