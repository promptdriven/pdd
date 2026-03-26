[Remotion]

# Section 7.6: Mold Glow Finale — The Mold Glows, the Plastic Fades

**Tool:** Remotion
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 0:16 - 0:20

## Visual Description
The visual culmination of the entire video's metaphor. The triangle diagram from spec 04 is still present, but now it transforms: the three vertices (PROMPT, TESTS, GROUNDING) intensify in brightness, each glowing strongly in their respective colors. The connecting edges brighten to match. The triangle becomes a luminous, powerful shape — the "mold."

Meanwhile, the code in the center dims further — becoming almost transparent, unremarkable, clearly subordinate. It's present but nobody is looking at it. The glow is on the triangle. The value is in the specification.

A subtle cross-section mold shape (inspired by injection molding) ghostly overlays the triangle, reinforcing the manufacturing metaphor. The mold walls glow. The plastic fill is dull.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid

### Chart/Visual Elements

#### Glowing Triangle (The Mold)
- Same triangle layout as spec 04
- Vertex nodes: respective colors now at full `1.0` opacity with outer glow
  - PROMPT: `#4A90D9`, glow `20px` blur, `0.35` opacity
  - TESTS: `#D9944A`, glow `20px` blur, `0.35` opacity
  - GROUNDING: `#5AAA6E`, glow `20px` blur, `0.35` opacity
- Edges: brightened to `#94A3B8` at `0.6`, `2px` — up from `#334155`
- Labels: full brightness, slightly larger — Inter, 18px, bold

#### Faded Code (The Plastic)
- Same center position, `(810, 400)`
- Code text: `#475569` at `0.2` — barely visible
- No animation — static, inert, present but unremarkable

#### Mold Cross-Section Overlay (Subtle)
- A ghostly injection-mold cross-section shape outlines the triangle area
- Color: `#E2E8F0` at `0.05`
- Suggests cavity walls around the code area
- Purely atmospheric — not labeled

### Animation Sequence
1. **Frame 0-30 (0-1s):** Triangle ramps from `0.3` opacity to full brightness. Each vertex intensifies sequentially (PROMPT → TESTS → GROUNDING, 10 frames each). Outer glows bloom.
2. **Frame 30-45 (1-1.5s):** Edges brighten. Mold cross-section overlay fades in at `0.05`. Code in center dims from `0.5` to `0.2`.
3. **Frame 45-90 (1.5-3s):** Hold on glowing triangle. Vertices pulse gently in unison. Code is static and faded. The contrast is stark: specification glows, code is forgettable.
4. **Frame 90-120 (3-4s):** Very slow fade begins — all elements dim `10%` toward the upcoming beat/black.

### Typography
- Vertex labels: Inter, 18px, bold (700), respective colors at `1.0`
- Code: JetBrains Mono, 12px, `#475569` at `0.2`

### Easing
- Vertex glow bloom: `easeOutQuad` over 10 frames each
- Edge brightening: `easeInOutCubic` over 15 frames
- Code dimming: `easeInQuad` over 15 frames
- Vertex pulse: `easeInOutSine` on 45-frame cycle
- Slow fade: `linear` over 30 frames

## Narration Sync
> "The code is just plastic."

Segment: `closing_004` (15.68s - 18.82s)

- **0:16** Triangle ramps to full glow — "The code..."
- **0:17** Code dims — "...is just plastic"
- **0:18-0:20** Hold on glowing mold, preparing for the beat

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Mold cross-section ghost overlay */}
    <Sequence from={30}>
      <FadeIn durationInFrames={15}>
        <MoldCrossSection x={960} y={480}
          width={700} height={400}
          color="#E2E8F0" opacity={0.05} />
      </FadeIn>
    </Sequence>

    {/* Triangle vertices — ramping to full glow */}
    {vertices.map((v, i) => (
      <Sequence key={i} from={i * 10}>
        <GlowBloom durationInFrames={10} easing="easeOutQuad"
          blurRadius={20} glowOpacity={0.35}>
          <VertexNode x={v.x} y={v.y} label={v.label}
            color={v.color} width={180} height={50}
            fontSize={18} radius={25} />
        </GlowBloom>
      </Sequence>
    ))}

    {/* Edges — brightening */}
    <Sequence from={30}>
      <AnimateColor from="#334155" to="#94A3B8"
        durationInFrames={15} easing="easeInOutCubic">
        <TriangleEdges vertices={vertexPositions}
          strokeWidth={2} opacity={0.6} />
      </AnimateColor>
    </Sequence>

    {/* Faded code — dimming */}
    <Sequence from={30}>
      <AnimateOpacity from={0.5} to={0.2}
        durationInFrames={15} easing="easeInQuad">
        <CodeBlock
          text={generatedCode}
          font="JetBrains Mono" size={12}
          color="#475569" x={810} y={400}
        />
      </AnimateOpacity>
    </Sequence>

    {/* Vertex pulse (hold phase) */}
    <Sequence from={45}>
      <Loop durationInFrames={45}>
        <PulseAll targets={vertexGlows}
          from={0.3} to={0.4}
          durationInFrames={45} easing="easeInOutSine" />
      </Loop>
    </Sequence>

    {/* Slow fade toward beat */}
    <Sequence from={90}>
      <FadeOut durationInFrames={30} easing="linear"
        targetOpacity={0.9} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "mold_glow_diagram",
  "vertices": [
    { "label": "PROMPT", "color": "#4A90D9", "glowRadius": 20 },
    { "label": "TESTS", "color": "#D9944A", "glowRadius": 20 },
    { "label": "GROUNDING", "color": "#5AAA6E", "glowRadius": 20 }
  ],
  "codeOpacity": 0.2,
  "moldOverlay": true,
  "backgroundColor": "#0A0F1A",
  "durationSeconds": 4,
  "narrationSegments": ["closing_004"]
}
```
