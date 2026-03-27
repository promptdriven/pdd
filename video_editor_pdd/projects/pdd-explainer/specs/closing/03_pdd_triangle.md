[Remotion]

# Section 7.3: PDD Triangle — Prompt, Tests, Grounding

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:02 - 0:08

## Visual Description

The three core components of Prompt-Driven Development materialize as an equilateral triangle on a deep navy background. **PROMPT** appears at the top vertex, glowing amber. **TESTS** appears at the bottom-left vertex, glowing teal. **GROUNDING** appears at the bottom-right vertex, glowing blue. Thin connecting lines draw between the three vertices, forming the triangle.

Once the triangle is established, code materializes in the center — syntax-highlighted lines appearing character by character as if being generated. The code pulses softly, indicating it is a product of the three surrounding constraints, not a hand-authored artifact. The triangle vertices glow in sync, reinforcing that the code is derived from their intersection.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: 60px spacing, `#1E293B` at 0.03 opacity

### Chart/Visual Elements

#### Triangle
- Center point: (960, 500)
- Vertex radius: 320px from center
- Top vertex (PROMPT): (960, 180)
- Bottom-left vertex (TESTS): (683, 680)
- Bottom-right vertex (GROUNDING): (1237, 680)
- Edge lines: 2px, `#334155` → `#4A5568` gradient, 0.6 opacity
- Vertex dots: 12px radius circles at each vertex

#### Vertex Labels
- PROMPT (top): `#D9944A` (amber), 24px Inter Bold
- TESTS (bottom-left): `#4AD9A0` (teal), 24px Inter Bold
- GROUNDING (bottom-right): `#4A90D9` (blue), 24px Inter Bold

#### Center Code Block
- Bounding box: 280x160px centered at (960, 480)
- Background: `#111827` at 0.8 opacity, 8px border-radius
- Code text: 13px JetBrains Mono
- Syntax colors: keywords `#C084FC`, strings `#86EFAC`, functions `#93C5FD`, punctuation `#94A3B8`

#### Glow Effects
- Each vertex: radial gradient glow, 60px radius, vertex color at 0.25 opacity
- Center code: soft `#E2E8F0` glow at 0.1 opacity, pulsing

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Top vertex fades in — PROMPT label appears with amber glow
2. **Frame 20-40 (0.67-1.33s):** Bottom-left vertex fades in — TESTS label appears with teal glow
3. **Frame 40-60 (1.33-2s):** Bottom-right vertex fades in — GROUNDING label appears with blue glow
4. **Frame 50-80 (1.67-2.67s):** Triangle edges draw in sequence: top→left, left→right, right→top
5. **Frame 80-130 (2.67-4.33s):** Code block fades in at center, lines type in character-by-character (2 frames/char)
6. **Frame 130-180 (4.33-6s):** Hold — vertex glows pulse in slow sine wave (60-frame cycle), code has subtle shimmer

### Typography
- Vertex labels: Inter, 24px, Bold (700), vertex-specific colors
- Code text: JetBrains Mono, 13px, Regular (400)

### Easing
- Vertex fade-in: `easeOut(quad)` over 20 frames
- Edge draw: `easeInOut(cubic)` over 15 frames each
- Code type-in: linear, 2 frames per character
- Glow pulse: `easeInOut(sine)` on 60-frame cycle

## Narration Sync
> "Encode intent. Tests preserve behavior."
> — closing_002 (2.14s – 7.58s)

> "Code is generated, verified, and"
> — closing_003 (7.82s – 10.94s, overlap during hold)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  {/* Triangle vertices */}
  <Sequence from={0} durationInFrames={60}>
    <TriangleVertex position="top" label="PROMPT" color="#D9944A" delay={0} />
    <TriangleVertex position="bottom-left" label="TESTS" color="#4AD9A0" delay={20} />
    <TriangleVertex position="bottom-right" label="GROUNDING" color="#4A90D9" delay={40} />
  </Sequence>
  {/* Triangle edges */}
  <Sequence from={50} durationInFrames={30}>
    <TriangleEdge vertices={triangleVertices} />
  </Sequence>
  {/* Center code generation */}
  <Sequence from={80} durationInFrames={100}>
    <GeneratedCodeBlock lines={codeLines} typeSpeed={2} />
  </Sequence>
  {/* Glow pulse overlay */}
  <Sequence from={130} durationInFrames={50}>
    <GlowPulse vertices={triangleVertices} cycleFrames={60} />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "remotion_animation",
  "componentId": "pdd_triangle",
  "durationFrames": 180,
  "fps": 30,
  "narrationSegments": ["closing_002", "closing_003"],
  "vertices": [
    { "label": "PROMPT", "position": [960, 180], "color": "#D9944A" },
    { "label": "TESTS", "position": [683, 680], "color": "#4AD9A0" },
    { "label": "GROUNDING", "position": [1237, 680], "color": "#4A90D9" }
  ],
  "codeLines": [
    "def calculate_total(items):",
    "    return sum(i.price for i in items)",
    "",
    "def apply_discount(total, pct):",
    "    return total * (1 - pct)"
  ]
}
```

---
