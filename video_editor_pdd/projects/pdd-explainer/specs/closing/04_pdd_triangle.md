[Remotion]

# Section 7.4: PDD Triangle — Prompt, Tests, Grounding

**Tool:** Remotion
**Duration:** ~7s (210 frames @ 30fps)
**Timestamp:** 0:07 - 0:14

## Visual Description

The three core components of PDD materialize as an equilateral triangle. PROMPT appears at the top vertex, glowing blue. TESTS appears at the bottom-left vertex, glowing green. GROUNDING appears at the bottom-right vertex, glowing amber. Connecting lines draw between them, forming the triangle.

As each narration line lands — "Prompts encode intent," "Tests preserve behavior," "Grounding maintains style" — the corresponding vertex pulses and its label brightens.

Then code materializes in the center of the triangle — lines of generated code streaming inward from all three vertices, converging at center. The code fills a contained area, shaped by the triangle. The message: code is an output of these three constraints.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Triangle
- Top vertex (PROMPT): (960, 200)
- Bottom-left vertex (TESTS): (480, 750)
- Bottom-right vertex (GROUNDING): (1440, 750)
- Edge lines: 2px, `#334155` at 0.4, drawn sequentially
- Interior fill: `#1E293B` at 0.08 (very subtle)

#### Vertex Labels
- "PROMPT": Inter, 22px, bold (700), `#60A5FA`, positioned above top vertex
- "TESTS": Inter, 22px, bold (700), `#4ADE80`, positioned below-left of bottom-left vertex
- "GROUNDING": Inter, 22px, bold (700), `#D9944A`, positioned below-right of bottom-right vertex

#### Vertex Icons
- Each vertex: glowing circle, 24px radius
  - PROMPT: `#60A5FA` at 0.6, glow radius 40px at 0.15
  - TESTS: `#4ADE80` at 0.6, glow radius 40px at 0.15
  - GROUNDING: `#D9944A` at 0.6, glow radius 40px at 0.15

#### Descriptor Text (appears with pulse)
- "encode intent" — Inter, 14px, italic, `#60A5FA` at 0.5, below PROMPT label
- "preserve behavior" — Inter, 14px, italic, `#4ADE80` at 0.5, below TESTS label
- "maintain style" — Inter, 14px, italic, `#D9944A` at 0.5, below GROUNDING label

#### Center Code Block
- Position: centered at (960, 520)
- Code lines: JetBrains Mono, 11px, `#E2E8F0` at 0.7
- 8-10 lines of pseudocode, appearing line by line
- Faint containment border: `#334155` at 0.1, matching triangle interior

### Animation Sequence
1. **Frame 0-30 (0-1s):** Top vertex (PROMPT) dot appears with glow. "PROMPT" label fades in. Edge lines begin drawing down-left and down-right. `easeOut(cubic)`.
2. **Frame 30-60 (1-2s):** Bottom-left vertex (TESTS) appears. Bottom-right vertex (GROUNDING) appears. Bottom edge draws. Triangle complete. `easeOut(cubic)`.
3. **Frame 60-90 (2-3s):** "Prompts encode intent" — PROMPT vertex pulses, descriptor text fades in.
4. **Frame 90-120 (3-4s):** "Tests preserve behavior" — TESTS vertex pulses, descriptor text fades in.
5. **Frame 120-150 (4-5s):** "Grounding maintains style" — GROUNDING vertex pulses, descriptor text fades in.
6. **Frame 150-195 (5-6.5s):** Code streams into center from all three vertices — small code tokens flow along the triangle edges toward center, accumulating as visible code lines. `easeOut(quad)`.
7. **Frame 195-210 (6.5-7s):** All elements stable. Code block in center. Triangle glows softly. Hold.

### Typography
- Vertex labels: Inter, 22px, bold (700)
- Descriptor text: Inter, 14px, italic (400)
- Center code: JetBrains Mono, 11px, regular (400), `#E2E8F0`

### Easing
- Vertex appear: `easeOut(cubic)` over 15 frames
- Edge draw: `easeInOut(cubic)` over 25 frames
- Vertex pulse: `easeInOut(sine)` over 20 frames (scale 1.0 → 1.2 → 1.0)
- Descriptor fade: `easeOut(quad)` over 15 frames
- Code stream: `easeOut(quad)` over 30 frames, staggered 3 frames per line

## Narration Sync
> "Prompts encode intent. Tests preserve behavior. Grounding maintains style."

Segment: `closing_002`

- **0:07** ("Prompts encode intent"): PROMPT vertex pulses, triangle forming
- **0:09** ("Tests preserve behavior"): TESTS vertex pulses
- **0:10** ("Grounding maintains style"): GROUNDING vertex pulses
- **0:12** (hold): Code streams into center, triangle complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={210}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Triangle edges */}
    <Sequence from={0}>
      <StrokeDraw duration={50}>
        <TriangleEdges
          vertices={[[960, 200], [480, 750], [1440, 750]]}
          color="#334155" opacity={0.4} strokeWidth={2} />
      </StrokeDraw>
    </Sequence>

    {/* PROMPT vertex */}
    <Sequence from={0}>
      <FadeIn duration={15}>
        <GlowDot cx={960} cy={200} r={24}
          color="#60A5FA" opacity={0.6} glowRadius={40} glowOpacity={0.15} />
        <Text text="PROMPT" font="Inter" size={22} weight={700}
          color="#60A5FA" x={960} y={160} align="center" />
      </FadeIn>
    </Sequence>

    {/* TESTS vertex */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <GlowDot cx={480} cy={750} r={24}
          color="#4ADE80" opacity={0.6} glowRadius={40} glowOpacity={0.15} />
        <Text text="TESTS" font="Inter" size={22} weight={700}
          color="#4ADE80" x={480} y={800} align="center" />
      </FadeIn>
    </Sequence>

    {/* GROUNDING vertex */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <GlowDot cx={1440} cy={750} r={24}
          color="#D9944A" opacity={0.6} glowRadius={40} glowOpacity={0.15} />
        <Text text="GROUNDING" font="Inter" size={22} weight={700}
          color="#D9944A" x={1440} y={800} align="center" />
      </FadeIn>
    </Sequence>

    {/* Descriptor text — staggered with narration */}
    <Sequence from={60}>
      <Pulse target="prompt" duration={20}>
        <FadeIn duration={15}>
          <Text text="encode intent" font="Inter" size={14}
            style="italic" color="#60A5FA" opacity={0.5}
            x={960} y={185} align="center" />
        </FadeIn>
      </Pulse>
    </Sequence>
    <Sequence from={90}>
      <Pulse target="tests" duration={20}>
        <FadeIn duration={15}>
          <Text text="preserve behavior" font="Inter" size={14}
            style="italic" color="#4ADE80" opacity={0.5}
            x={480} y={825} align="center" />
        </FadeIn>
      </Pulse>
    </Sequence>
    <Sequence from={120}>
      <Pulse target="grounding" duration={20}>
        <FadeIn duration={15}>
          <Text text="maintain style" font="Inter" size={14}
            style="italic" color="#D9944A" opacity={0.5}
            x={1440} y={825} align="center" />
        </FadeIn>
      </Pulse>
    </Sequence>

    {/* Code streaming to center */}
    <Sequence from={150}>
      <CodeStream
        sources={[[960, 200], [480, 750], [1440, 750]]}
        target={[960, 520]}
        codeLines={GENERATED_CODE}
        font="JetBrains Mono" fontSize={11}
        color="#E2E8F0" opacity={0.7}
        streamDuration={30} stagger={3} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "chartId": "pdd_triangle",
  "vertices": [
    { "id": "prompt", "label": "PROMPT", "position": [960, 200], "color": "#60A5FA", "descriptor": "encode intent" },
    { "id": "tests", "label": "TESTS", "position": [480, 750], "color": "#4ADE80", "descriptor": "preserve behavior" },
    { "id": "grounding", "label": "GROUNDING", "position": [1440, 750], "color": "#D9944A", "descriptor": "maintain style" }
  ],
  "centerElement": {
    "type": "generated_code",
    "position": [960, 520],
    "font": "JetBrains Mono"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["closing_002"]
}
```

---
