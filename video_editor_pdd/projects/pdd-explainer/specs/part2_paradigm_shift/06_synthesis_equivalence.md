[Remotion]

# Section 2.6: Synthesis Equivalence — Non-Deterministic Output, Deterministic Function

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 9:41 - 9:59

## Visual Description
A diagram demonstrates Synopsys-style formal equivalence checking. At the top center, a single Verilog spec block sits as the source of truth. Two arrows diverge downward to the left and right, each leading to a DIFFERENT gate layout — visually distinct arrangements of the same logic, illustrating non-deterministic synthesis. Both outputs look different but a verification bridge connects them at the bottom: a green checkmark badge with "Functionally Identical ✓" confirms formal equivalence. Then the visual morphs into the PDD parallel: the Verilog block transforms into a prompt file, the gate layouts transform into code files, and the verification badge stays — drawing the explicit connection: "Synopsys → PDD. Same architecture."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Spec Block (Top Center)**
  - Position: centered at (960, 140)
  - Rounded rectangle 400px x 100px, border `#D9944A` 2px, fill `rgba(217,148,74,0.08)`
  - Text: "Verilog Spec" — `#D9944A`, 20px, bold, centered
  - Subtext: `module counter(...)` — JetBrains Mono, 14px, `#94A3B8`
- **Diverging Arrows**
  - Two curved arrows from bottom of spec block, one curving left to (360, 380), one curving right to (1560, 380)
  - Stroke: `rgba(255,255,255,0.3)`, 2px, dashed
  - Labels at midpoint: "Run 1" (left), "Run 2" (right) — `#94A3B8`, 14px
- **Gate Layout A (Left)**
  - Position: centered at (360, 480)
  - Rounded rectangle 340px x 200px, border `#4A90D9` 1.5px, fill `rgba(74,144,217,0.05)`
  - Contains: ~8 gate symbols in a HORIZONTAL arrangement, wires flowing left-to-right
  - Label below: "Output A" — `#4A90D9`, 16px
- **Gate Layout B (Right)**
  - Position: centered at (1560, 480)
  - Rounded rectangle 340px x 200px, border `#4A90D9` 1.5px, fill `rgba(74,144,217,0.05)`
  - Contains: ~8 gate symbols in a VERTICAL arrangement, wires flowing top-to-bottom (visually DIFFERENT from A)
  - Label below: "Output B" — `#4A90D9`, 16px
- **Equivalence Bridge**
  - Horizontal connector between bottom of Layout A and Layout B at Y=620
  - Dashed line `rgba(42,161,152,0.5)`, 2px
  - Center badge: Circle 60px diameter, fill `#2AA198`, checkmark icon `#FFFFFF`
  - Label below badge: "Functionally Identical" — `#2AA198`, 18px, bold
- **PDD Morph Phase**
  - Spec block text morphs: "Verilog Spec" → "Prompt File" (color stays `#D9944A`)
  - Gate layouts morph: gate symbols dissolve, replaced by code line representations (horizontal bars)
  - Layout labels: "Output A" → "Generated Code v1", "Output B" → "Generated Code v2"
  - New bottom label: "Synopsys → PDD. Same architecture." — `#FBBF24`, 20px, bold, at Y=760

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Spec block fades in and draws border. Text appears
2. **Frame 40-80 (1.33-2.67s):** Two diverging arrows draw outward from spec block. "Run 1" and "Run 2" labels fade in
3. **Frame 80-160 (2.67-5.33s):** Gate Layout A assembles on left (gates snap in one by one). Gate Layout B assembles on right (different arrangement). "Output A" and "Output B" labels appear
4. **Frame 160-180 (5.33-6s):** Brief hold — viewer sees the two different outputs
5. **Frame 180-240 (6-8s):** Equivalence bridge draws: dashed line extends from left to right. Checkmark badge scales in from 0→1.2→1.0 at center. "Functionally Identical" fades in below
6. **Frame 240-300 (8-10s):** Hold on the complete Synopsys diagram
7. **Frame 300-380 (10-12.67s):** PDD morph: Spec block text cross-fades to "Prompt File". Gate symbols dissolve into code-line bars. Layout labels cross-fade to "Generated Code v1/v2". Equivalence badge stays unchanged
8. **Frame 380-440 (12.67-14.67s):** Bottom label "Synopsys → PDD. Same architecture." types in, character by character
9. **Frame 440-540 (14.67-18s):** Hold at final state

### Typography
- Spec Block Title: Inter, 20px, bold (700), `#D9944A`
- Spec Block Code: JetBrains Mono, 14px, regular (400), `#94A3B8`
- Run Labels: Inter, 14px, regular (400), `#94A3B8`
- Output Labels: Inter, 16px, medium (500), `#4A90D9`
- Equivalence Label: Inter, 18px, bold (700), `#2AA198`
- Bottom Parallel Label: Inter, 20px, bold (700), `#FBBF24`

### Easing
- Spec block draw: `easeOut(cubic)`
- Arrow diverge: `easeOut(quad)`
- Gate assembly: `easeOut(back(1.1))` per gate, staggered 3 frames apart
- Checkmark badge scale: `easeOut(back(1.5))`
- PDD morph cross-fade: `easeInOut(cubic)`
- Bottom label typewriter: `linear`

## Narration Sync
> "Now, synthesis was non-deterministic. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time."
> "What Synopsys did was wrap a verification toolchain around the generator. Formal equivalence checking, using SAT and SMT solvers to produce mathematical proof that the output, whatever it looked like, behaved identically to the spec. The gates were different every time. The function was the same every time."
> "Synopsys turned hardware descriptions into verified silicon. PDD turns prompts into verified software. Same architecture. Specification in, verified artifact out."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Spec Block */}
  <Sequence from={0} durationInFrames={40}>
    <SpecBlock
      x={960} y={140}
      title="Verilog Spec"
      code="module counter(...)"
      borderColor="#D9944A"
    />
  </Sequence>

  {/* Diverging Arrows */}
  <Sequence from={40} durationInFrames={40}>
    <DivergingArrows
      fromX={960} fromY={190}
      toLeftX={360} toRightX={1560} toY={380}
      labels={["Run 1", "Run 2"]}
    />
  </Sequence>

  {/* Gate Layouts */}
  <Sequence from={80} durationInFrames={80}>
    <GateLayout
      x={360} y={480} arrangement="horizontal"
      gateCount={8} label="Output A" color="#4A90D9"
    />
    <GateLayout
      x={1560} y={480} arrangement="vertical"
      gateCount={8} label="Output B" color="#4A90D9"
    />
  </Sequence>

  {/* Equivalence Bridge */}
  <Sequence from={180} durationInFrames={60}>
    <EquivalenceBridge
      leftX={360} rightX={1560} y={620}
      badgeColor="#2AA198"
      label="Functionally Identical"
    />
  </Sequence>

  {/* PDD Morph */}
  <Sequence from={300} durationInFrames={80}>
    <MorphTransition
      specFrom="Verilog Spec" specTo="Prompt File"
      layoutFrom="gates" layoutTo="codeLines"
      labelFrom={["Output A", "Output B"]}
      labelTo={["Generated Code v1", "Generated Code v2"]}
    />
  </Sequence>

  {/* Bottom Label */}
  <Sequence from={380} durationInFrames={60}>
    <TypewriterLabel
      text="Synopsys → PDD. Same architecture."
      y={760} color="#FBBF24"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "specBlock": {
    "position": { "x": 960, "y": 140 },
    "width": 400,
    "height": 100,
    "title": "Verilog Spec",
    "code": "module counter(...)",
    "borderColor": "#D9944A",
    "fillColor": "rgba(217,148,74,0.08)"
  },
  "divergingArrows": {
    "leftTarget": { "x": 360, "y": 380 },
    "rightTarget": { "x": 1560, "y": 380 },
    "labels": ["Run 1", "Run 2"],
    "strokeColor": "rgba(255,255,255,0.3)"
  },
  "gateLayouts": {
    "a": {
      "position": { "x": 360, "y": 480 },
      "arrangement": "horizontal",
      "gateCount": 8,
      "label": "Output A",
      "color": "#4A90D9"
    },
    "b": {
      "position": { "x": 1560, "y": 480 },
      "arrangement": "vertical",
      "gateCount": 8,
      "label": "Output B",
      "color": "#4A90D9"
    }
  },
  "equivalence": {
    "y": 620,
    "badgeColor": "#2AA198",
    "badgeDiameter": 60,
    "label": "Functionally Identical"
  },
  "pddMorph": {
    "specTo": "Prompt File",
    "layoutTo": ["Generated Code v1", "Generated Code v2"],
    "bottomLabel": "Synopsys → PDD. Same architecture.",
    "bottomLabelColor": "#FBBF24"
  }
}
```

---
