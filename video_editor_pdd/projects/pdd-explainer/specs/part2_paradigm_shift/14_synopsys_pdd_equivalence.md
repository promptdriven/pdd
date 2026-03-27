[title:]

# Section 2.14: Synopsys ↔ PDD Equivalence Overlay

**Tool:** Title
**Duration:** ~13s (390 frames @ 30fps)
**Timestamp:** 2:47 - 3:00

## Visual Description

A clean text overlay that makes the direct analogy explicit. Two lines appear, stacked:

**Line 1:** "Synopsys: specification in → verified hardware out."
**Line 2:** "PDD: prompt in → verified software out."

Both lines use a consistent format — the company/method name in a colored accent, the description in clean white. An animated arrow connects "specification" to "prompt" and "hardware" to "software" — showing the structural equivalence. The background stays deep navy-black. This is a thesis statement, not decoration.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: Faint blueprint grid, `#1E293B` at 0.03

### Chart/Visual Elements

#### Line 1 (Synopsys)
- "Synopsys:" — Inter, 32px, bold (700), `#4A90D9` (blue)
- "specification in → verified hardware out." — Inter, 32px, regular (400), `#E2E8F0`
- Position: centered at y: 440
- Arrow symbol (→): `#64748B`

#### Line 2 (PDD)
- "PDD:" — Inter, 32px, bold (700), `#D9944A` (amber)
- "prompt in → verified software out." — Inter, 32px, regular (400), `#E2E8F0`
- Position: centered at y: 520
- Arrow symbol (→): `#64748B`

#### Connecting Lines (equivalence mapping)
- Dotted line from "specification" to "prompt": `#5AAA6E` at 0.4, 1px dashed
- Dotted line from "hardware" to "software": `#5AAA6E` at 0.4, 1px dashed

#### Subtitle
- "Same architecture." — Inter, 18px, italic, `#94A3B8` at 0.6, centered at y: 600

### Animation Sequence
1. **Frame 0-60 (0-2s):** Line 1 types in. "Synopsys:" in blue appears first, then the rest.
2. **Frame 60-120 (2-4s):** Line 2 types in. "PDD:" in amber appears first, then the rest.
3. **Frame 120-180 (4-6s):** Dotted connecting lines draw between "specification"↔"prompt" and "hardware"↔"software".
4. **Frame 180-240 (6-8s):** "Same architecture." subtitle fades in.
5. **Frame 240-330 (8-11s):** Hold. The parallel is explicit.
6. **Frame 330-390 (11-13s):** Fade out.

### Typography
- Names: Inter, 32px, bold (700), respective accent colors
- Description: Inter, 32px, regular (400), `#E2E8F0`
- Arrows: Inter, 32px, `#64748B`
- Subtitle: Inter, 18px, italic, `#94A3B8` at 0.6

### Easing
- Type-in: linear, 2 frames per character
- Connecting lines: `easeInOut(cubic)` over 30 frames
- Subtitle fade: `easeOut(quad)` over 30 frames
- Fade out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Synopsys turned hardware descriptions into verified silicon. PDD turns prompts into verified software. Same architecture. Specification in, verified artifact out."

Segment: `part2_paradigm_shift_014`

- **179.48s** (seg 014): Line 1 types in — "Synopsys turned hardware descriptions"
- **183.0s**: Line 2 types in — "PDD turns prompts into verified software"
- **186.0s**: Connecting lines — "Same architecture"
- **189.0s**: Subtitle — "Specification in, verified artifact out"
- **192.66s** (seg 014 ends): Hold, begin fade

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={390}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Line 1: Synopsys */}
    <Sequence from={0}>
      <TypeWriter
        segments={[
          { text: "Synopsys: ", color: "#4A90D9", weight: 700 },
          { text: "specification in → verified hardware out.", color: "#E2E8F0", weight: 400 }
        ]}
        font="Inter" size={32} charDelay={2}
        x={960} y={440} align="center"
      />
    </Sequence>

    {/* Line 2: PDD */}
    <Sequence from={60}>
      <TypeWriter
        segments={[
          { text: "PDD: ", color: "#D9944A", weight: 700 },
          { text: "prompt in → verified software out.", color: "#E2E8F0", weight: 400 }
        ]}
        font="Inter" size={32} charDelay={2}
        x={960} y={520} align="center"
      />
    </Sequence>

    {/* Equivalence connecting lines */}
    <Sequence from={120}>
      <DashedLine from="specification" to="prompt"
        color="#5AAA6E" opacity={0.4} drawDuration={30} />
      <DashedLine from="hardware" to="software"
        color="#5AAA6E" opacity={0.4} drawDuration={30} />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={180}>
      <FadeIn duration={30}>
        <Text text="Same architecture." font="Inter" size={18}
          style="italic" color="#94A3B8" opacity={0.6}
          x={960} y={600} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={330}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "text_overlay",
  "chartId": "synopsys_pdd_equivalence",
  "lines": [
    {
      "accent": { "text": "Synopsys:", "color": "#4A90D9" },
      "body": "specification in → verified hardware out."
    },
    {
      "accent": { "text": "PDD:", "color": "#D9944A" },
      "body": "prompt in → verified software out."
    }
  ],
  "subtitle": "Same architecture.",
  "equivalenceMappings": [
    { "from": "specification", "to": "prompt" },
    { "from": "hardware", "to": "software" }
  ],
  "narrationSegments": ["part2_paradigm_shift_014"]
}
```

---
