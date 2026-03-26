[Remotion]

# Section 3.11: Z3 Formal Proof — Same Math as Chip Verification

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 2:24 - 2:44

## Visual Description

A sidebar annotation screen. The main visual is a comparison layout showing the conceptual equivalence between chip formal verification and PDD's use of Z3.

On the left: a chip die photo (stylized) with the label "Synopsys Formality" and a small Synopsys-style logo icon. Mathematical proof symbols float nearby: ∀, ∃, ⊢, ≡.

On the right: a code module with the label "PDD + Z3" and a Z3-style logo icon. The same mathematical symbols appear.

Between them, an equals sign or "≡" glows, connecting the two — same technology class, different domain. An annotation reads: "PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input."

Below: "Not sampling. Mathematical proof." pulses with emphasis.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Left — Chip Verification
- Position: centered at (350, 400)
- Chip die: stylized rectangle 200×200px, `#4A90D9` at 0.1 fill, `#4A90D9` at 0.3 border, inner grid pattern
- Label: "Synopsys Formality" — Inter, 14px, bold, `#4A90D9` at 0.7
- Logo placeholder: 30×30px, `#4A90D9` at 0.4, simplified chip icon
- Math symbols: ∀, ∃, ⊢ floating at various positions, Inter, 24px, `#4A90D9` at 0.2

#### Right — PDD Z3
- Position: centered at (1570, 400)
- Code module: rounded rect 200×200px, `#2DD4BF` at 0.1 fill, `#2DD4BF` at 0.3 border, code lines inside
- Label: "PDD + Z3" — Inter, 14px, bold, `#2DD4BF` at 0.7
- Logo placeholder: 30×30px, `#2DD4BF` at 0.4, simplified solver icon
- Math symbols: ∀, ∃, ≡ floating, Inter, 24px, `#2DD4BF` at 0.2

#### Equivalence Connector
- Position: centered at (960, 400)
- "≡" symbol: Inter, 72px, bold, `#A78BFA` at 0.6, with glow 15px radius
- Dashed lines from left to ≡ to right, `#A78BFA` at 0.2

#### Main Annotation
- Position: centered at (960, 650)
- Text block: max-width 800px, Inter, 16px, `#E2E8F0` at 0.7
- "PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input."

#### Emphasis Line
- Position: centered at (960, 750)
- "Not sampling. Mathematical proof." — Inter, 20px, bold, `#A78BFA` at 0.8
- Subtle pulse glow

#### Domain Label
- "Same math as billion-dollar tapeouts." — Inter, 12px, italic, `#94A3B8` at 0.4, y: 800

### Animation Sequence
1. **Frame 0-90 (0-3s):** Left chip die draws in. Synopsys label and math symbols float in.
2. **Frame 90-180 (3-6s):** Right code module draws in. Z3 label and math symbols float in.
3. **Frame 180-270 (6-9s):** "≡" symbol appears at center with glow bloom. Dashed connection lines draw.
4. **Frame 270-390 (9-13s):** Main annotation text fades in, word by word or line by line.
5. **Frame 390-480 (13-16s):** "Not sampling. Mathematical proof." appears with emphasis pulse.
6. **Frame 480-600 (16-20s):** Hold. Domain label fades in. Everything subtly pulses.

### Typography
- Labels: Inter, 14px, bold (700), respective side colors
- Math symbols: Inter, 24px, respective side colors at 0.2
- Equivalence: Inter, 72px, bold (700), `#A78BFA`
- Annotation: Inter, 16px, `#E2E8F0` at 0.7
- Emphasis: Inter, 20px, bold (700), `#A78BFA`
- Domain note: Inter, 12px, italic, `#94A3B8` at 0.4

### Easing
- Chip/module draw: `easeOut(cubic)` over 40 frames
- Math symbols float: `easeOut(sine)` drift, various delays
- Equivalence bloom: `easeOut(cubic)` over 30 frames
- Text fade-in: `easeOut(quad)` over 20 frames per line
- Emphasis pulse: `easeInOut(sine)` on 40-frame cycle
- Connection lines: `easeInOut(quad)` over 30 frames

## Narration Sync
> "And some of those walls aren't just tested — they're proven. PDD uses Z3, the same class of SMT solver that the chip industry uses for formal equivalence checking, to mathematically prove that properties hold for every possible input. Not sampling. Mathematical proof. The chip design analogy isn't a metaphor. It's the same technology."

Segment: `part3_mold_has_three_parts_016`

- **2:24** ("some of those walls aren't just tested"): Chip die and Z3 module appear
- **2:32** ("PDD uses Z3"): Equivalence connector appears, annotation text
- **2:40** ("Not sampling. Mathematical proof."): Emphasis line pulses

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Left — Chip Verification */}
    <Sequence from={0}>
      <StrokeDraw duration={40}>
        <ChipDie x={350} y={400} size={200}
          fill="#4A90D9" fillOpacity={0.1}
          stroke="#4A90D9" strokeOpacity={0.3} />
      </StrokeDraw>
      <FadeIn duration={20} delay={40}>
        <Text text="Synopsys Formality" font="Inter" size={14}
          weight={700} color="#4A90D9" opacity={0.7}
          x={350} y={540} align="center" />
      </FadeIn>
      <FloatingSymbols symbols={["∀", "∃", "⊢"]}
        color="#4A90D9" opacity={0.2} cx={350} cy={400} />
    </Sequence>

    {/* Right — PDD Z3 */}
    <Sequence from={90}>
      <StrokeDraw duration={40}>
        <CodeModule x={1570} y={400} size={200}
          fill="#2DD4BF" fillOpacity={0.1}
          stroke="#2DD4BF" strokeOpacity={0.3} />
      </StrokeDraw>
      <FadeIn duration={20} delay={40}>
        <Text text="PDD + Z3" font="Inter" size={14}
          weight={700} color="#2DD4BF" opacity={0.7}
          x={1570} y={540} align="center" />
      </FadeIn>
      <FloatingSymbols symbols={["∀", "∃", "≡"]}
        color="#2DD4BF" opacity={0.2} cx={1570} cy={400} />
    </Sequence>

    {/* Equivalence connector */}
    <Sequence from={180}>
      <GlowBloom duration={30}>
        <Text text="≡" font="Inter" size={72}
          weight={700} color="#A78BFA" opacity={0.6}
          x={960} y={400} align="center" />
      </GlowBloom>
      <DashedLine from={[500, 400]} to={[900, 400]} color="#A78BFA" opacity={0.2} />
      <DashedLine from={[1020, 400]} to={[1420, 400]} color="#A78BFA" opacity={0.2} />
    </Sequence>

    {/* Annotation */}
    <Sequence from={270}>
      <FadeIn duration={40}>
        <TextBlock x={960} y={650} maxWidth={800}
          text="PDD also uses Z3 — the same class of SMT solver used in chip verification — to formally prove properties hold for every possible input."
          font="Inter" size={16} color="#E2E8F0" opacity={0.7}
          align="center" />
      </FadeIn>
    </Sequence>

    {/* Emphasis */}
    <Sequence from={390}>
      <PulsingText
        text="Not sampling. Mathematical proof."
        font="Inter" size={20} weight={700}
        color="#A78BFA" opacity={0.8}
        x={960} y={750} align="center"
        pulseCycle={40} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "annotation_overlay",
  "diagramId": "z3_formal_proof",
  "comparison": {
    "left": { "label": "Synopsys Formality", "domain": "chip_verification", "color": "#4A90D9" },
    "right": { "label": "PDD + Z3", "domain": "code_verification", "color": "#2DD4BF" },
    "equivalence": { "symbol": "≡", "color": "#A78BFA" }
  },
  "emphasisLine": "Not sampling. Mathematical proof.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_016"]
}
```

---
