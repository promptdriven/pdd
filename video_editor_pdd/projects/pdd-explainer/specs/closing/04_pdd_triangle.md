[Remotion]

# Section 7.4: PDD Triangle — The Core Visual Thesis

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:33 - 24:43

## Visual Description

The core visual thesis of the entire video materializes as a clean equilateral triangle. Three nodes form at the vertices, each representing one component of the PDD "mold": PROMPT (top, blue), TESTS (bottom-left, amber), GROUNDING (bottom-right, green). The triangle draws itself edge by edge, then fills with generated code lines at its center — thin, gray, unremarkable.

Each node gets a one-line descriptor that fades in as the narration calls it out: "Encodes intent" (prompt), "Preserve behavior" (tests), "Maintains style" (grounding). The descriptors are small and subordinate to the node labels — the triangle itself is the message.

The triangle sits centered against a dark background with a very subtle radial glow emanating outward. The glow is dim — the triangle is being introduced, not yet at its climactic brightness. That comes later.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A1225` (deep navy-black)
- Radial glow: centered, `#1E293B` at 0.04, radius 600px

### Chart/Visual Elements

#### Triangle Frame
- Equilateral triangle, centered at (960, 520)
- Side length: 500px
- Vertices:
  - Top (PROMPT): (960, 280)
  - Bottom-left (TESTS): (710, 713)
  - Bottom-right (GROUNDING): (1210, 713)
- Edge stroke: 2px, `#475569` at 0.6
- Edge glow: 4px Gaussian blur, `#475569` at 0.06

#### Node: PROMPT (Top)
- Circle: 20px radius, filled `#4A90D9`, stroke 2px `#4A90D9` at 0.8
- Label: "PROMPT" — Inter, 16px, bold (700), `#4A90D9`, centered above node at y: 248
- Descriptor: "Encodes intent" — Inter, 11px, `#4A90D9` at 0.4, centered at y: 232
- Subtle pulse: radius oscillates 20px → 22px → 20px over 60 frames, `easeInOut(sine)`

#### Node: TESTS (Bottom-Left)
- Circle: 20px radius, filled `#D9944A`, stroke 2px `#D9944A` at 0.8
- Label: "TESTS" — Inter, 16px, bold (700), `#D9944A`, centered below node at y: 748
- Descriptor: "Preserve behavior" — Inter, 11px, `#D9944A` at 0.4, centered at y: 768
- Same subtle pulse

#### Node: GROUNDING (Bottom-Right)
- Circle: 20px radius, filled `#5AAA6E`, stroke 2px `#5AAA6E` at 0.8
- Label: "GROUNDING" — Inter, 16px, bold (700), `#5AAA6E`, centered below node at y: 748
- Descriptor: "Maintains style" — Inter, 11px, `#5AAA6E` at 0.4, centered at y: 768
- Same subtle pulse

#### Generated Code (Center)
- 8-10 thin horizontal lines at triangle center, staggered widths (60-180px)
- Color: `#94A3B8` at 0.15
- Position: clustered around (960, 520), slight random vertical offsets
- The code lines are deliberately unremarkable — they're output, not the focus

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background and radial glow fade in. Stillness.
2. **Frame 30-60 (1-2s):** Top node (PROMPT) appears — circle scales from 0 with bounce. Label "PROMPT" fades in. Edge draws downward-left.
3. **Frame 60-90 (2-3s):** Bottom-left node (TESTS) appears with bounce. Label fades in. Edge draws rightward to bottom-right.
4. **Frame 90-120 (3-4s):** Bottom-right node (GROUNDING) appears with bounce. Label fades in. Final edge draws upward to top, completing the triangle.
5. **Frame 120-170 (4-5.7s):** Descriptors fade in staggered: "Encodes intent" (frame 120), "Preserve behavior" (frame 135), "Maintains style" (frame 150).
6. **Frame 170-230 (5.7-7.7s):** Code lines materialize at center — thin gray lines appear one by one with slight fade, filling the interior. The code is generated, emerging from the mold.
7. **Frame 230-300 (7.7-10s):** All three nodes begin subtle pulse. Hold. The triangle is established as the video's central icon.

### Typography
- Node labels: Inter, 16px, bold (700), respective node colors
- Descriptors: Inter, 11px, respective node colors at 0.4
- Code lines: decorative (no text — just horizontal bars representing code)

### Easing
- Node circle appear: `easeOut(back(1.6))` scale 0→1 over 15 frames
- Edge draw: `easeInOut(cubic)` over 25 frames per edge
- Label fade: `easeOut(quad)` over 12 frames
- Descriptor fade: `easeOut(quad)` over 15 frames
- Code line appear: `easeOut(quad)` opacity, 8 frames each, 4-frame stagger
- Node pulse: `easeInOut(sine)` continuous, 60-frame period

## Narration Sync
> "Prompts encode intent. Tests preserve behavior. Grounding maintains style."

Segment: `closing_003`

- **24:33** ("Prompts encode intent"): Top node (PROMPT) appears with label and descriptor
- **24:36** ("Tests preserve behavior"): Bottom-left node (TESTS) appears
- **24:39** ("Grounding maintains style"): Bottom-right node (GROUNDING) appears, triangle complete
- **24:41** (visual: code fills center): Generated code lines appear inside triangle

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A1225' }}>
    <RadialGlow center={[960, 520]} radius={600}
      color="#1E293B" opacity={0.04} />

    {/* Triangle edges — draw sequentially */}
    <Sequence from={30}>
      <DrawEdge from={[960, 280]} to={[710, 713]}
        color="#475569" opacity={0.6} width={2}
        glow={{ blur: 4, opacity: 0.06 }}
        drawDuration={25} easing="easeInOut(cubic)" />
    </Sequence>
    <Sequence from={60}>
      <DrawEdge from={[710, 713]} to={[1210, 713]}
        color="#475569" opacity={0.6} width={2}
        glow={{ blur: 4, opacity: 0.06 }}
        drawDuration={25} easing="easeInOut(cubic)" />
    </Sequence>
    <Sequence from={90}>
      <DrawEdge from={[1210, 713]} to={[960, 280]}
        color="#475569" opacity={0.6} width={2}
        glow={{ blur: 4, opacity: 0.06 }}
        drawDuration={25} easing="easeInOut(cubic)" />
    </Sequence>

    {/* PROMPT node — top */}
    <Sequence from={30}>
      <ScaleIn duration={15} easing="easeOut(back(1.6))">
        <NodeCircle center={[960, 280]} radius={20}
          fill="#4A90D9" stroke="#4A90D9" strokeOpacity={0.8}
          pulse={{ min: 20, max: 22, period: 60, delay: 200 }} />
      </ScaleIn>
      <FadeIn duration={12}>
        <Text text="PROMPT" font="Inter" size={16} weight={700}
          color="#4A90D9" x={960} y={248} align="center" />
      </FadeIn>
      <Sequence from={90}>
        <FadeIn duration={15}>
          <Text text="Encodes intent" font="Inter" size={11}
            color="#4A90D9" opacity={0.4} x={960} y={232} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* TESTS node — bottom-left */}
    <Sequence from={60}>
      <ScaleIn duration={15} easing="easeOut(back(1.6))">
        <NodeCircle center={[710, 713]} radius={20}
          fill="#D9944A" stroke="#D9944A" strokeOpacity={0.8}
          pulse={{ min: 20, max: 22, period: 60, delay: 200 }} />
      </ScaleIn>
      <FadeIn duration={12}>
        <Text text="TESTS" font="Inter" size={16} weight={700}
          color="#D9944A" x={710} y={748} align="center" />
      </FadeIn>
      <Sequence from={75}>
        <FadeIn duration={15}>
          <Text text="Preserve behavior" font="Inter" size={11}
            color="#D9944A" opacity={0.4} x={710} y={768} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* GROUNDING node — bottom-right */}
    <Sequence from={90}>
      <ScaleIn duration={15} easing="easeOut(back(1.6))">
        <NodeCircle center={[1210, 713]} radius={20}
          fill="#5AAA6E" stroke="#5AAA6E" strokeOpacity={0.8}
          pulse={{ min: 20, max: 22, period: 60, delay: 200 }} />
      </ScaleIn>
      <FadeIn duration={12}>
        <Text text="GROUNDING" font="Inter" size={16} weight={700}
          color="#5AAA6E" x={1210} y={748} align="center" />
      </FadeIn>
      <Sequence from={60}>
        <FadeIn duration={15}>
          <Text text="Maintains style" font="Inter" size={11}
            color="#5AAA6E" opacity={0.4} x={1210} y={768} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Generated code lines at center */}
    <Sequence from={170}>
      <CodeLines center={[960, 520]} count={9}
        widthRange={[60, 180]} color="#94A3B8" opacity={0.15}
        stagger={4} fadeDuration={8} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "geometric_diagram",
  "diagramId": "pdd_triangle",
  "shape": "equilateral_triangle",
  "center": [960, 520],
  "sideLength": 500,
  "nodes": [
    {
      "id": "prompt",
      "label": "PROMPT",
      "descriptor": "Encodes intent",
      "position": "top",
      "coordinates": [960, 280],
      "color": "#4A90D9"
    },
    {
      "id": "tests",
      "label": "TESTS",
      "descriptor": "Preserve behavior",
      "position": "bottom_left",
      "coordinates": [710, 713],
      "color": "#D9944A"
    },
    {
      "id": "grounding",
      "label": "GROUNDING",
      "descriptor": "Maintains style",
      "position": "bottom_right",
      "coordinates": [1210, 713],
      "color": "#5AAA6E"
    }
  ],
  "centerContent": "generated_code_lines",
  "backgroundColor": "#0A1225",
  "narrationSegments": ["closing_003"]
}
```

---
