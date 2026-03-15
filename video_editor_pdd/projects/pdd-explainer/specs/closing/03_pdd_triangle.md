[Remotion]

# Section 7.3: The PDD Triangle — Three Components

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:33 - 24:43

## Visual Description
The screen transitions to a dark cinematic background. Three glowing nodes appear at the vertices of an equilateral triangle, each representing a core PDD component: PROMPT (top, blue), TESTS (bottom-left, amber), GROUNDING (bottom-right, green). The triangle assembles vertex by vertex, timed precisely to the narration's three declarative sentences. As each vertex appears, a label and a thin connecting edge draw in. Once all three vertices are connected, code materializes in the center of the triangle — generated from the three. The code text is neutral gray with a faint blue tint, visually subordinate to the glowing triangle vertices.

This is the thesis distilled to its simplest geometric form — the specification triangle, where value lives.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep dark `#0A0F1A` (solid)
- Grid lines: None

### Chart/Visual Elements
- **Triangle Vertices (equilateral, centered at 960, 520):**
  - **PROMPT (top):** Circle node, 24px radius, `#4A90D9` fill, `#4A90D9` glow (16px blur, 40% opacity). Position: (960, 300)
  - **TESTS (bottom-left):** Circle node, 24px radius, `#D9944A` fill, `#D9944A` glow (16px blur, 40% opacity). Position: (660, 720)
  - **GROUNDING (bottom-right):** Circle node, 24px radius, `#5AAA6E` fill, `#5AAA6E` glow (16px blur, 40% opacity). Position: (1260, 720)

- **Triangle Edges:**
  - PROMPT→TESTS: 2px line, gradient from `#4A90D9` to `#D9944A`
  - TESTS→GROUNDING: 2px line, gradient from `#D9944A` to `#5AAA6E`
  - GROUNDING→PROMPT: 2px line, gradient from `#5AAA6E` to `#4A90D9`

- **Vertex Labels:**
  - "PROMPT" — centered above top vertex, `#4A90D9`
  - "TESTS" — centered below bottom-left vertex, `#D9944A`
  - "GROUNDING" — centered below bottom-right vertex, `#5AAA6E`

- **Center Code Block:**
  - 6 lines of faint monospace code text, `#94A3B8` at 50% opacity
  - Contained within an implicit rectangle ~280x140px centered at (960, 520)
  - Subtle blue tint overlay `#4A90D9` at 5% opacity
  - Lines represent generic function code (syntax-highlighted but muted)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Fade in from black. Empty dark canvas.
2. **Frame 15-60 (0.5-2.0s):** Narration: "Prompts encode intent." — PROMPT vertex fades in (opacity 0→1, scale 0.5→1.0) with blue glow bloom. Label "PROMPT" fades in 10 frames after node.
3. **Frame 60-105 (2.0-3.5s):** Narration: "Tests preserve behavior." — TESTS vertex fades in with amber glow. Edge draws from PROMPT→TESTS (line grows from PROMPT position toward TESTS). Label "TESTS" fades in.
4. **Frame 105-150 (3.5-5.0s):** Narration: "Grounding maintains style." — GROUNDING vertex fades in with green glow. Edges draw: TESTS→GROUNDING and GROUNDING→PROMPT simultaneously. Label "GROUNDING" fades in. Triangle complete.
5. **Frame 150-180 (5.0-6.0s):** Triangle pulses once (all edges brighten to full opacity then settle to 70%). The interior of the triangle fills with a very subtle gradient (center lighter `#0A0F1A` at 95% → transparent).
6. **Frame 180-240 (6.0-8.0s):** Code materializes in center. Lines type in sequentially (3 frames apart), each with a brief flash matching the nearest vertex color. The code is clearly generated from the triangle — visual causality.
7. **Frame 240-300 (8.0-10.0s):** Hold. All elements visible. Gentle ambient pulse on vertex glows (opacity 0.3→0.5→0.3, 60-frame cycle). Code sits subordinate in center.

### Typography
- Vertex labels: Inter, 20px, semi-bold (600), matching vertex color, letter-spacing: 3px
- Center code: JetBrains Mono, 13px, `#94A3B8` at 50% opacity

### Easing
- Vertex appear (scale + opacity): `easeOut(back)` with overshoot 1.2
- Glow bloom: `easeOut(quad)`
- Edge draw: `easeInOut(cubic)`
- Label fade: `easeOut(quad)`
- Triangle pulse: `easeInOut(sin)`
- Code line type-in: `easeOut(quad)`
- Ambient glow pulse: `easeInOut(sin)`

## Narration Sync
> "Prompts encode intent."
> "Tests preserve behavior."
> "Grounding maintains style."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <Background color="#0A0F1A" />

  {/* PROMPT vertex — top */}
  <Sequence from={15}>
    <GlowNode
      position={[960, 300]}
      color="#4A90D9"
      radius={24}
      glowBlur={16}
      durationInFrames={30}
    />
    <Sequence from={10}>
      <FadeInLabel text="PROMPT" position={[960, 260]} color="#4A90D9" />
    </Sequence>
  </Sequence>

  {/* TESTS vertex — bottom-left */}
  <Sequence from={60}>
    <GlowNode position={[660, 720]} color="#D9944A" radius={24} glowBlur={16} durationInFrames={30} />
    <Sequence from={10}>
      <FadeInLabel text="TESTS" position={[660, 760]} color="#D9944A" />
    </Sequence>
  </Sequence>

  {/* GROUNDING vertex — bottom-right */}
  <Sequence from={105}>
    <GlowNode position={[1260, 720]} color="#5AAA6E" radius={24} glowBlur={16} durationInFrames={30} />
    <Sequence from={10}>
      <FadeInLabel text="GROUNDING" position={[1260, 760]} color="#5AAA6E" />
    </Sequence>
  </Sequence>

  {/* Triangle Edges */}
  <Sequence from={60}>
    <DrawEdge from={[960, 300]} to={[660, 720]} gradient={["#4A90D9", "#D9944A"]} durationInFrames={30} />
  </Sequence>
  <Sequence from={105}>
    <DrawEdge from={[660, 720]} to={[1260, 720]} gradient={["#D9944A", "#5AAA6E"]} durationInFrames={30} />
    <DrawEdge from={[1260, 720]} to={[960, 300]} gradient={["#5AAA6E", "#4A90D9"]} durationInFrames={30} />
  </Sequence>

  {/* Triangle pulse */}
  <Sequence from={150}>
    <TrianglePulse vertices={[[960,300],[660,720],[1260,720]]} durationInFrames={30} />
  </Sequence>

  {/* Center Code Materialization */}
  <Sequence from={180}>
    <CenterCodeBlock
      position={[960, 520]}
      lines={generatedCodeLines}
      staggerFrames={3}
      textColor="#94A3B8"
      textOpacity={0.5}
      tintColor="#4A90D9"
      tintOpacity={0.05}
    />
  </Sequence>

  {/* Ambient glow cycle */}
  <Sequence from={240}>
    <AmbientGlowPulse
      nodes={[
        { position: [960, 300], color: "#4A90D9" },
        { position: [660, 720], color: "#D9944A" },
        { position: [1260, 720], color: "#5AAA6E" }
      ]}
      cycleFrames={60}
      opacityRange={[0.3, 0.5]}
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "triangle": {
    "center": [960, 520],
    "vertices": {
      "prompt": { "position": [960, 300], "color": "#4A90D9", "label": "PROMPT" },
      "tests": { "position": [660, 720], "color": "#D9944A", "label": "TESTS" },
      "grounding": { "position": [1260, 720], "color": "#5AAA6E", "label": "GROUNDING" }
    },
    "edges": [
      { "from": "prompt", "to": "tests", "gradient": ["#4A90D9", "#D9944A"] },
      { "from": "tests", "to": "grounding", "gradient": ["#D9944A", "#5AAA6E"] },
      { "from": "grounding", "to": "prompt", "gradient": ["#5AAA6E", "#4A90D9"] }
    ],
    "edgeWidth": 2
  },
  "nodeStyle": {
    "radius": 24,
    "glowBlur": 16,
    "glowOpacity": 0.4
  },
  "centerCode": {
    "lineCount": 6,
    "textColor": "#94A3B8",
    "textOpacity": 0.5,
    "tintColor": "#4A90D9",
    "tintOpacity": 0.05
  },
  "backgroundColor": "#0A0F1A"
}
```

---
