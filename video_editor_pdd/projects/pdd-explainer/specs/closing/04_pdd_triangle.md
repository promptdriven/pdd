[Remotion]

# Section 7.4: PDD Triangle — Prompt, Tests, Grounding

**Tool:** Remotion
**Duration:** ~5s (150 frames @ 30fps)
**Timestamp:** 0:08 - 0:13

## Visual Description
The three components of the PDD "mold" appear as an equilateral triangle diagram. PROMPT sits at the top vertex (blue), TESTS at the bottom-left (amber), GROUNDING at the bottom-right (green). Each vertex is a rounded label node with a subtle glow in its respective color.

As the narration delivers "Prompts encode intent. Tests preserve behavior. Grounding maintains style." — each vertex highlights in sequence with a pulse. Then lines connect all three vertices forming the triangle frame.

In the center of the triangle, generated code materializes — lines of monospace text in neutral gray, appearing character by character. The code is clearly an *output* of the three surrounding components — smaller, less vivid, subordinate.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: none

### Chart/Visual Elements

#### Triangle Vertices
| Vertex | Label | Color | Position (x, y) |
|--------|-------|-------|-----------------|
| Top | PROMPT | `#4A90D9` (blue) | (960, 200) |
| Bottom-left | TESTS | `#D9944A` (amber) | (520, 720) |
| Bottom-right | GROUNDING | `#5AAA6E` (green) | (1400, 720) |

- Node shape: rounded rectangle, `180×50px`, corner radius `25px`
- Node fill: respective color at `0.15`, border: respective color at `0.8`, `2px`
- Label: Inter, 16px, bold, respective color at `1.0`

#### Subtitle Labels
| Vertex | Subtitle | Color |
|--------|----------|-------|
| Top | "encode intent" | `#4A90D9` at `0.6` |
| Bottom-left | "preserve behavior" | `#D9944A` at `0.6` |
| Bottom-right | "maintain style" | `#5AAA6E` at `0.6` |

- Font: Inter, 13px, regular, positioned 30px below each vertex node

#### Connecting Lines
- Three edges forming the triangle
- Stroke: `#334155` at `0.4`, `1.5px`, drawing from vertex to vertex
- Draw animation: each line draws over 15 frames

#### Center Code Block
- Position: centered in triangle, `(960, 480)`
- Monospace text block: 5-6 lines of representative code
- Font: JetBrains Mono, 12px, `#64748B` at `0.5`
- Slight blue tint inherited from prompt color: `#64748B`
- Fades in after triangle is fully formed

### Animation Sequence
1. **Frame 0-30 (0-1s):** PROMPT vertex fades in and pulses once (scale `1.0→1.08→1.0`). Subtitle "encode intent" appears.
2. **Frame 30-60 (1-2s):** TESTS vertex fades in and pulses. Subtitle "preserve behavior" appears.
3. **Frame 60-90 (2-3s):** GROUNDING vertex fades in and pulses. Subtitle "maintain style" appears.
4. **Frame 90-110 (3-3.7s):** Triangle edges draw in sequence: top→bottom-left, bottom-left→bottom-right, bottom-right→top.
5. **Frame 110-150 (3.7-5s):** Code materializes in center — characters appear in a fast type-on effect. The code is visually subordinate, clearly an output.

### Typography
- Vertex labels: Inter, 16px, bold (700), respective vertex color
- Subtitles: Inter, 13px, regular (400), respective vertex color at `0.6`
- Center code: JetBrains Mono, 12px, `#64748B` at `0.5`

### Easing
- Vertex fade-in: `easeOutQuad` over 15 frames
- Vertex pulse: `easeInOutSine` over 15 frames
- Edge draw: `easeInOutCubic` over 15 frames each
- Code type-on: linear, 1 frame per 3 characters

## Narration Sync
> "Prompts encode intent. Tests preserve behavior. Grounding maintains style."

Segment: `closing_002` (2.94s - 12.28s) — this spec covers the mid-portion

- **0:08** PROMPT vertex appears — "Prompts encode intent"
- **0:09** TESTS vertex appears — "Tests preserve behavior"
- **0:10** GROUNDING vertex appears — "Grounding maintains style"
- **0:11** Triangle completes, code fills center

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* PROMPT vertex */}
    <Sequence from={0}>
      <FadeAndPulse durationInFrames={30} pulseScale={1.08}>
        <VertexNode x={960} y={200} label="PROMPT"
          color="#4A90D9" width={180} height={50} radius={25} />
        <Text text="encode intent" font="Inter" size={13}
          color="#4A90D9" opacity={0.6} x={960} y={260} align="center" />
      </FadeAndPulse>
    </Sequence>

    {/* TESTS vertex */}
    <Sequence from={30}>
      <FadeAndPulse durationInFrames={30} pulseScale={1.08}>
        <VertexNode x={520} y={720} label="TESTS"
          color="#D9944A" width={180} height={50} radius={25} />
        <Text text="preserve behavior" font="Inter" size={13}
          color="#D9944A" opacity={0.6} x={520} y={780} align="center" />
      </FadeAndPulse>
    </Sequence>

    {/* GROUNDING vertex */}
    <Sequence from={60}>
      <FadeAndPulse durationInFrames={30} pulseScale={1.08}>
        <VertexNode x={1400} y={720} label="GROUNDING"
          color="#5AAA6E" width={180} height={50} radius={25} />
        <Text text="maintain style" font="Inter" size={13}
          color="#5AAA6E" opacity={0.6} x={1400} y={780} align="center" />
      </FadeAndPulse>
    </Sequence>

    {/* Triangle edges */}
    <Sequence from={90}>
      <DrawLine from={[960,225]} to={[520,695]}
        color="#334155" opacity={0.4} width={1.5}
        durationInFrames={15} easing="easeInOutCubic" />
    </Sequence>
    <Sequence from={95}>
      <DrawLine from={[520,745]} to={[1400,745]}
        color="#334155" opacity={0.4} width={1.5}
        durationInFrames={15} easing="easeInOutCubic" />
    </Sequence>
    <Sequence from={100}>
      <DrawLine from={[1400,695]} to={[960,225]}
        color="#334155" opacity={0.4} width={1.5}
        durationInFrames={15} easing="easeInOutCubic" />
    </Sequence>

    {/* Center code */}
    <Sequence from={110}>
      <TypeWriter
        lines={[
          "def validate_email(addr: str) -> bool:",
          "    pattern = compile(EMAIL_RE)",
          "    if not pattern.match(addr):",
          "        raise InvalidEmail(addr)",
          "    return check_domain(addr)"
        ]}
        font="JetBrains Mono" size={12}
        color="#64748B" opacity={0.5}
        x={810} y={430} lineHeight={22}
        charsPerFrame={3}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "triangle_diagram",
  "vertices": [
    { "label": "PROMPT", "subtitle": "encode intent", "color": "#4A90D9", "position": [960, 200] },
    { "label": "TESTS", "subtitle": "preserve behavior", "color": "#D9944A", "position": [520, 720] },
    { "label": "GROUNDING", "subtitle": "maintain style", "color": "#5AAA6E", "position": [1400, 720] }
  ],
  "edgeColor": "#334155",
  "centerCode": true,
  "backgroundColor": "#0A0F1A",
  "durationSeconds": 5,
  "narrationSegments": ["closing_002"]
}
```
