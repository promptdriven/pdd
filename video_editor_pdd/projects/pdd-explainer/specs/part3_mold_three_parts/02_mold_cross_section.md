[Remotion]

# Section 3.2: Mold Cross-Section — Three Regions Reveal

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 0:29 - 0:45

## Visual Description

A technical blueprint-style cross-section of an injection mold fills the screen. The mold is rendered in a clean engineering-diagram style — precise lines, labeled dimensions, and three clearly delineated regions. The mold starts as a single outline, then three regions highlight one by one with color fills and labels:

1. **Walls (Tests)** — The inner boundary surfaces glow amber, labeled "Tests: The Walls"
2. **Nozzle (Prompt)** — The injection nozzle at the top glows teal, labeled "Prompt: The Specification"
3. **Material (Grounding)** — The fill material area glows purple, labeled "Grounding: The Material"

Each region activates with a pulse and a label callout line. The cross-section is rendered with blueprint-line aesthetics — white/light blue on dark background with grid lines suggesting technical precision.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.08

### Chart/Visual Elements

#### Mold Outline
- Outer shell: Rectangular with rounded injection channel, centered at (960, 540)
- Dimensions: 700×400px
- Stroke: `#4A90D9` at 0.4, 2px
- Inner cavity: 500×250px, centered within shell

#### Region 1 — Walls (Tests)
- Vertical and horizontal boundary lines inside the cavity
- Six wall segments at varying positions, creating a complex cavity shape
- Color: `#D9944A` (amber) fill at 0.15, stroke at 0.6
- Label: "TESTS: THE WALLS" — Inter, 16px, bold, `#D9944A`
- Callout line: 1px dashed `#D9944A` at 0.4 from walls to label

#### Region 2 — Nozzle (Prompt)
- Tapered funnel shape at top of mold, feeding into cavity
- Color: `#2DD4BF` (teal) fill at 0.15, stroke at 0.6
- Label: "PROMPT: THE SPECIFICATION" — Inter, 16px, bold, `#2DD4BF`
- Callout line: 1px dashed `#2DD4BF` at 0.4 from nozzle to label

#### Region 3 — Material (Grounding)
- Amorphous fill area inside the cavity between walls
- Color: `#A78BFA` (purple) fill at 0.15, stroke at 0.6
- Label: "GROUNDING: THE MATERIAL" — Inter, 16px, bold, `#A78BFA`
- Callout line: 1px dashed `#A78BFA` at 0.4 from material to label

#### Subtitle
- "Three types of capital you're accumulating" — Inter, 14px, `#94A3B8` at 0.6, centered at y: 920

### Animation Sequence
1. **Frame 0-60 (0-2s):** Mold outline draws with stroke animation, blueprint-style. Grid visible.
2. **Frame 60-120 (2-4s):** Hold on complete outline. Subtle dimension annotations appear.
3. **Frame 120-200 (4-6.67s):** Region 1 (Walls) fills with amber glow. Callout line draws. Label appears.
4. **Frame 200-280 (6.67-9.33s):** Region 2 (Nozzle) fills with teal glow. Callout line draws. Label appears.
5. **Frame 280-360 (9.33-12s):** Region 3 (Material) fills with purple glow. Callout line draws. Label appears.
6. **Frame 360-420 (12-14s):** All three regions pulse together. Subtitle fades in.
7. **Frame 420-480 (14-16s):** Hold. All regions active, subtle synchronized pulse.

### Typography
- Region labels: Inter, 16px, bold (700), respective region color
- Subtitle: Inter, 14px, `#94A3B8` at 0.6
- Dimension annotations: JetBrains Mono, 10px, `#64748B` at 0.3

### Easing
- Mold outline draw: `easeInOut(cubic)` over 60 frames
- Region fill: `easeOut(cubic)` over 30 frames
- Callout line draw: `easeOut(quad)` over 20 frames
- Label fade-in: `easeOut(quad)` over 15 frames
- Synchronized pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "The prompt is your mold. The code is just plastic."
> "Now let's get precise. Because 'prompt is the mold' is a nice metaphor, but it's incomplete."
> "In PDD, the mold has three components. Three types of capital you're accumulating."

Segments: `part3_mold_three_parts_004`, `part3_mold_three_parts_005`, `part3_mold_three_parts_006`

- **0:29** ("The prompt is your mold"): Mold outline begins drawing
- **0:43** ("three components"): Regions begin highlighting one by one
- **0:53** ("Three types of capital"): Subtitle appears, all regions active

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.08} />

    {/* Mold outline */}
    <Sequence from={0}>
      <StrokeDraw duration={60}>
        <MoldOutline
          cx={960} cy={540}
          outerWidth={700} outerHeight={400}
          innerWidth={500} innerHeight={250}
          color="#4A90D9" opacity={0.4} strokeWidth={2} />
      </StrokeDraw>
    </Sequence>

    {/* Region 1: Walls (Tests) */}
    <Sequence from={120}>
      <RegionReveal
        region="walls"
        fill="#D9944A" fillOpacity={0.15}
        stroke="#D9944A" strokeOpacity={0.6}
        label="TESTS: THE WALLS"
        labelFont="Inter" labelSize={16}
        calloutDuration={20} fillDuration={30} />
    </Sequence>

    {/* Region 2: Nozzle (Prompt) */}
    <Sequence from={200}>
      <RegionReveal
        region="nozzle"
        fill="#2DD4BF" fillOpacity={0.15}
        stroke="#2DD4BF" strokeOpacity={0.6}
        label="PROMPT: THE SPECIFICATION"
        labelFont="Inter" labelSize={16}
        calloutDuration={20} fillDuration={30} />
    </Sequence>

    {/* Region 3: Material (Grounding) */}
    <Sequence from={280}>
      <RegionReveal
        region="material"
        fill="#A78BFA" fillOpacity={0.15}
        stroke="#A78BFA" strokeOpacity={0.6}
        label="GROUNDING: THE MATERIAL"
        labelFont="Inter" labelSize={16}
        calloutDuration={20} fillDuration={30} />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="Three types of capital you're accumulating"
          font="Inter" size={14} color="#94A3B8" opacity={0.6}
          x={960} y={920} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "mold_cross_section",
  "regions": [
    { "id": "walls", "label": "Tests: The Walls", "color": "#D9944A", "role": "constraints" },
    { "id": "nozzle", "label": "Prompt: The Specification", "color": "#2DD4BF", "role": "specification" },
    { "id": "material", "label": "Grounding: The Material", "color": "#A78BFA", "role": "style" }
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_004", "part3_mold_three_parts_005", "part3_mold_three_parts_006"]
}
```

---
