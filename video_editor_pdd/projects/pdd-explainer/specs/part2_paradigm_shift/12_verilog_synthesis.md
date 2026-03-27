[Remotion]

# Section 2.12: Verilog Synthesis — Schematic to Code

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 2:22 - 2:34

## Visual Description

A transformation animation. The dense hand-drawn schematic from the previous scene dissolves. In its place, clean Verilog code appears — crisp monospace text on a dark background. The code is readable, structured, concise. Below the code block, a stylized "Synopsys Design Compiler" processor icon appears — a geometric chip shape with an input arrow (Verilog code) and an output arrow (gate-level netlist). The netlist flows out automatically as a stream of gate symbols — automatically generated, no human hand needed.

The visual progression: illegible schematic → readable code → automatic synthesis. The abstraction level rises.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: Faint blueprint grid, `#1E293B` at 0.05

### Chart/Visual Elements

#### Verilog Code Block (upper portion)
- Code container: `#1E293B` background, rounded corners 8px, padding 24px
- Code text: JetBrains Mono, 16px, syntax-highlighted
  - Keywords (`module`, `always`, `assign`): `#C792EA` (purple)
  - Identifiers: `#E2E8F0` (white)
  - Comments: `#546E7A` (gray)
  - Numbers: `#F78C6C` (orange)
- Position: centered, y: 150, width: 800px

#### Synthesis Processor (center)
- Geometric chip shape: `#4A90D9` outline, 2px, with `#4A90D9` at 0.1 fill
- Label: "SYNTHESIS", Inter 14px, `#94A3B8`, centered inside chip
- Input arrow (left): flowing code symbols → into chip
- Output arrow (right): gate symbols flowing out →

#### Gate-Level Netlist (lower portion)
- Stream of gate symbols (AND, OR, NOT shapes): `#5AAA6E`, small vector icons
- Flowing rightward in a continuous stream
- Dense but orderly — machine-generated precision

### Animation Sequence
1. **Frame 0-60 (0-2s):** Dense schematic dissolves (particle effect, breaking into fragments that scatter). Dark background takes over.
2. **Frame 60-150 (2-5s):** Verilog code types in line by line. Syntax highlighting appears as each line completes. Clean, readable.
3. **Frame 150-210 (5-7s):** Synthesis chip icon fades in below the code. "SYNTHESIS" label appears. Input arrow starts pulsing.
4. **Frame 210-300 (7-10s):** Code symbols flow into the chip. Gate symbols stream out the other side. The transformation is automatic and continuous.
5. **Frame 300-360 (10-12s):** Gate stream continues. The output is automatic, flowing, machine-generated. Hold.

### Typography
- Code: JetBrains Mono, 16px, regular (400), syntax colors per above
- Synthesis label: Inter, 14px, semi-bold (600), `#94A3B8`
- Code comment: JetBrains Mono, 16px, `#546E7A`

### Easing
- Schematic dissolve: `easeIn(quad)` over 60 frames
- Code type-in: linear, 3 frames per character
- Chip fade-in: `easeOut(cubic)` over 30 frames
- Gate stream: linear continuous flow
- Arrow pulse: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "A hardware description language. You described what you wanted the chip to do, and a synthesis tool generated the gates."

Segment: `part2_paradigm_shift_011` (tail)

- **135.0s**: Schematic dissolves
- **137.0s**: Verilog code types in — "hardware description language"
- **139.0s**: Synthesis icon appears — "synthesis tool"
- **141.0s**: Gates flowing out — "generated the gates"
- **142.28s** (seg 011 ends): Hold, gate stream continues

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Schematic dissolve */}
    <Sequence from={0} durationInFrames={60}>
      <ParticleDissolve duration={60}>
        <SchematicImage src="dense_schematic.svg" />
      </ParticleDissolve>
    </Sequence>

    {/* Verilog code block */}
    <Sequence from={60}>
      <CodeBlock
        language="verilog"
        code={verilogExample}
        font="JetBrains Mono" size={16}
        background="#1E293B" borderRadius={8}
        typeSpeed={3} x={560} y={150} width={800}
      />
    </Sequence>

    {/* Synthesis processor */}
    <Sequence from={150}>
      <FadeIn duration={30}>
        <SynthesisChip
          outlineColor="#4A90D9" fillOpacity={0.1}
          label="SYNTHESIS" x={960} y={550}
        />
      </FadeIn>
    </Sequence>

    {/* Gate stream output */}
    <Sequence from={210}>
      <GateStream
        gateColor="#5AAA6E" direction="right"
        density={20} speed={2}
        x={1100} y={550} width={700}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "synthesis_animation",
  "chartId": "verilog_synthesis",
  "codeLanguage": "verilog",
  "codeSample": "module counter(\\n  input clk, rst,\\n  output reg [7:0] count\\n);\\n  always @(posedge clk)\\n    if (rst) count <= 0;\\n    else count <= count + 1;\\nendmodule",
  "synthesisStages": ["code_input", "synthesis_process", "gate_output"],
  "narrationSegments": ["part2_paradigm_shift_011"]
}
```

---
