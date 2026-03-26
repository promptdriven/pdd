[title:]

# Section 2.1: The Paradigm Shift — Section Title Card

**Tool:** Title
**Duration:** ~49s (1470 frames @ 30fps)
**Timestamp:** 0:00 - 0:49

## Visual Description

A section title card that bridges the recap of Part 1's economic argument into Part 2's paradigm shift thesis. "THE PARADIGM" appears first in large bold weight, then "SHIFT" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of an injection mold cross-section sits at very low opacity — the outline of a mold cavity with liquid flowing into it, foreshadowing the manufacturing metaphor. Background is deep navy-black, consistent with the Part 1 visual language.

The title holds across four narration segments: the recap of Part 1 findings ("Let me put together what I just showed you"), the context-window insight, the "category shift" declaration, and the "try it yourself" challenge. The card fades out as the narration pivots to "There's a pattern here..."

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
- Mold outline: simplified cross-section path, `#8B5CF6` at 0.03, 2px stroke
- Flow channel: bezier from top-center into cavity, `#8B5CF6` at 0.02, 1.5px stroke
- Cavity glow: subtle radial at center (~960, 540), `#8B5CF6` at 0.02, 40px radius

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 2" label fades in. Ghost mold silhouette draws with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE PARADIGM" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "SHIFT" fades in with 10px upward slide.
6. **Frame 90-1410 (3-47s):** Hold. Ghost mold pulses subtly. Title stays visible throughout recap narration.
7. **Frame 1410-1470 (47-49s):** Title and elements fade out, transitioning to factory floor.

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
- Final fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Let me put together what I just showed you."
> "You saw that prompts are a fraction the size of the code they govern... working in prompt space gives you two things at once."
> "A bigger window AND a smarter model. Not one or the other. Both. That's not an incremental improvement. That's a category shift."
> "Try it yourself. Take your favorite LLM, give it a hard coding problem as code, then give it the same problem described in natural language. The natural language version will win."

Segments: `part2_paradigm_shift_001`, `part2_paradigm_shift_002`, `part2_paradigm_shift_003`, `part2_paradigm_shift_004`

- **0.00s** (seg 001): Title card begins fade-in
- **2.84s** (seg 001 ends): "THE PARADIGM" typing visible
- **3.00s** (seg 002): Title fully visible, hold during recap
- **25.88s** (seg 002 ends): Hold
- **26.00s** (seg 003): "Category shift" — title pulses briefly
- **37.02s** (seg 004): "Try it yourself" — still holding
- **48.62s** (seg 004 ends): Title begins fade-out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1470}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost mold silhouette */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <MoldSilhouette color="#8B5CF6" opacity={0.03} strokeWidth={2} />
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

    {/* Fade out */}
    <Sequence from={1410}>
      <FadeOut duration={60} />
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
    { "shape": "mold_silhouette", "color": "#8B5CF6", "role": "injection_mold_preview" }
  ],
  "narrationSegments": ["part2_paradigm_shift_001", "part2_paradigm_shift_002", "part2_paradigm_shift_003", "part2_paradigm_shift_004"]
}
```

---
