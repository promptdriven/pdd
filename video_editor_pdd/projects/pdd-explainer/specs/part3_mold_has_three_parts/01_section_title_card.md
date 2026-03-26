[title:]

# Section 3.1: The Mold Has Three Parts — Section Title Card

**Tool:** Title
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 0:00 - 0:14

## Visual Description

A section title card introducing the three-part mold concept. "THE MOLD HAS" appears first in large bold weight, then "THREE PARTS" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost cross-section of an injection mold sits at low opacity — three distinct regions subtly color-coded: walls in amber, nozzle in teal, and material flow in purple. The three regions pulse sequentially, previewing the structure of the section. Background is deep navy-black, consistent with Parts 1-2.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "THE MOLD HAS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "THREE PARTS" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 240px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "PART 3" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (mold cross-section)
- Mold outer shell: rectangular outline (500×250px) centered at (960, 540), `#4A90D9` at 0.03, 2px stroke
- Wall region (left): vertical line segments inside mold, `#D9944A` at 0.04, 2px stroke
- Nozzle region (top): tapered triangle pointing down into mold, `#2DD4BF` at 0.04, 2px stroke
- Material region (center): amorphous flow shape inside mold, `#A78BFA` at 0.03, 2px stroke

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** "PART 3" label fades in. Ghost mold cross-section draws with stroke-dashoffset.
3. **Frame 40-60 (1.33-2s):** "THE MOLD HAS" types on character-by-character (2 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "THREE PARTS" fades in with 10px upward slide.
6. **Frame 90-200 (3-6.67s):** Ghost mold regions pulse sequentially — walls amber, then nozzle teal, then material purple. Each pulse 30 frames.
7. **Frame 200-420 (6.67-14s):** Hold. Subtle overall pulse on cross-section.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "THREE PARTS" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Ghost mold draw: `easeInOut(cubic)` over 30 frames
- Region pulses: `easeInOut(sine)` on 30-frame intervals
- Hold pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."
> "In PDD, the mold has three components. Three types of capital you're accumulating."

Segments: `part3_mold_has_three_parts_001`, `part3_mold_has_three_parts_002`

- **0:00** ("Now let's get precise"): Title card begins fade-in
- **1.50s** ("nice metaphor"): "THE MOLD HAS" typing on screen
- **3.00s** ("three components"): "THREE PARTS" revealed
- **6.67s** ("Three types of capital"): Three regions pulsing sequentially

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost mold cross-section */}
    <Sequence from={15}>
      <StrokeDraw duration={30}>
        <MoldCrossSection
          shell={{ cx: 960, cy: 540, width: 500, height: 250 }}
          walls={{ color: "#D9944A", opacity: 0.04 }}
          nozzle={{ color: "#2DD4BF", opacity: 0.04 }}
          material={{ color: "#A78BFA", opacity: 0.03 }}
          strokeWidth={2} />
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
      <DrawLine from={[840, 505]} to={[1080, 505]}
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

    {/* Sequential region pulses */}
    <Sequence from={90}>
      <RegionPulse region="walls" color="#D9944A" startFrame={0} duration={30} />
      <RegionPulse region="nozzle" color="#2DD4BF" startFrame={30} duration={30} />
      <RegionPulse region="material" color="#A78BFA" startFrame={60} duration={30} />
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
    { "shape": "mold_shell", "color": "#4A90D9", "component": "outer_shell" },
    { "shape": "mold_walls", "color": "#D9944A", "component": "test_walls" },
    { "shape": "mold_nozzle", "color": "#2DD4BF", "component": "prompt_nozzle" },
    { "shape": "mold_material", "color": "#A78BFA", "component": "grounding_material" }
  ],
  "narrationSegments": ["part3_mold_has_three_parts_001", "part3_mold_has_three_parts_002"]
}
```

---
