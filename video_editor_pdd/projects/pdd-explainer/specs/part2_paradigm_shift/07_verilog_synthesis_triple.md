[Remotion]

# Section 2.7: Verilog Synthesis Triple — Non-Deterministic Output

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 9:25 - 9:43

## Visual Description

An animated diagram demonstrating the non-deterministic nature of hardware synthesis — the same Verilog code produces different gate-level netlists each time, but all are functionally equivalent. This is the conceptual foundation for PDD.

The animation has two phases:

**Phase 1 — The Transition:** A hand-drawn schematic (from the previous scene) dissolves into clean Verilog code on screen. Below the code, a Synopsys Design Compiler icon processes it. A gate-level netlist (simplified circuit diagram of AND/OR/NOT gates with connections) flows out automatically. The message: humans stopped drawing gates; a tool generates them from a higher-level description.

**Phase 2 — Non-Determinism:** The same Verilog code block runs through synthesis three times, shown in three columns. Three visibly different gate-level netlists appear side by side — different arrangements of gates, different wiring, different layouts. All different. Then a green checkmark and label "Functionally equivalent" appears over each. The gates differ; the behavior is identical.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Faint circuit-board trace grid, 20px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Phase 1 — Schematic → Verilog

##### Hand-Drawn Schematic (dissolving)
- Position: centered at (960, 300), 600x300px
- Style: sketchy, slightly uneven lines, `#64748B` at 0.5
- Content: transistor symbols, connecting wires (suggests hand-drawn)
- Dissolve: particles scatter from top-left to bottom-right

##### Verilog Code Block
- Position: centered at (960, 250), 500x200px
- Background: `#1E293B` at 0.3, 4px rounded corners
- Code text: JetBrains Mono, 11px, syntax-colored:
  - Keywords (`module`, `always`, `assign`): `#C792EA` (purple)
  - Identifiers: `#E2E8F0`
  - Comments: `#546E7A` at 0.6
  - Strings/numbers: `#C3E88D` (green)
- Example code:
  ```
  module counter(
    input clk, rst,
    output reg [7:0] count
  );
    always @(posedge clk)
      if (rst) count <= 0;
      else count <= count + 1;
  endmodule
  ```

##### Synopsys Compiler Icon
- Position: centered at (960, 480), 60x60px
- Shape: gear/processor icon, `#4A90D9` at 0.6
- Label: "Synthesis" — Inter, 11px, `#4A90D9` at 0.5
- Arrow from code → compiler → netlist, `#475569` at 0.3, 1px

##### Gate-Level Netlist (single)
- Position: centered at (960, 650), 400x200px
- Content: simplified AND/OR/NOT gates connected by wires
- Gate shapes: standard logic symbols, `#94A3B8` at 0.4, 1.5px stroke
- Connecting wires: `#475569` at 0.3, 1px

#### Phase 2 — Triple Synthesis

##### Three Columns
- Column 1: x: 280, Column 2: x: 960, Column 3: x: 1640
- Each column width: 450px

##### Shared Verilog Code (top, spanning all columns)
- Same code block as Phase 1, but at y: 100, full width
- Label above: "Same input" — Inter, 12px, `#64748B` at 0.4

##### Three Arrows Down
- From code block to each column, `#475569` at 0.3, 1px
- Small gear icon at each arrow midpoint, `#4A90D9` at 0.4

##### Three Different Netlists
- Each at y: 500, 400x250px
- **Netlist A:** 6 gates, horizontal layout, compact routing
  - Gates: `#94A3B8` at 0.5, wires: `#475569` at 0.3
- **Netlist B:** 8 gates, vertical layout, longer wires, one redundant gate
  - Gates: `#94A3B8` at 0.5, wires: `#475569` at 0.3
- **Netlist C:** 5 gates, mixed layout, optimized routing
  - Gates: `#94A3B8` at 0.5, wires: `#475569` at 0.3
- All three VISIBLY DIFFERENT — different gate counts, different arrangements

##### Equivalence Checkmarks
- Green checkmark: `#5AAA6E`, 30x30px, centered above each netlist
- Label: "Functionally equivalent" — Inter, 12px, `#5AAA6E` at 0.6
- Connecting line between all three checkmarks, dashed, `#5AAA6E` at 0.2

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Hand-drawn schematic visible (remnant from previous scene). It begins dissolving — particles scatter.
2. **Frame 40-90 (1.33-3s):** Verilog code block fades in where the schematic was. Lines appear one by one (typing effect). Syntax coloring activates.
3. **Frame 90-130 (3-4.33s):** Arrow draws from code → compiler icon → netlist position. Compiler icon pulses.
4. **Frame 130-180 (4.33-6s):** Gate-level netlist draws itself below the compiler. Gates appear, wires connect. Automatic generation.
5. **Frame 180-220 (6-7.33s):** Transition: single layout crossfades to triple-column layout. Code block moves to top. "Same input" label appears.
6. **Frame 220-300 (7.33-10s):** Three arrows draw down simultaneously. Three compiler icons pulse. Three netlists begin drawing — each different.
7. **Frame 300-400 (10-13.33s):** All three netlists complete. The visual differences are obvious — different gate counts, different layouts, different wiring. Hold for a beat to let the viewer notice.
8. **Frame 400-460 (13.33-15.33s):** Green checkmarks pop in above each netlist. "Functionally equivalent" label fades in. Dashed connecting line draws between checkmarks.
9. **Frame 460-540 (15.33-18s):** Hold. The three different outputs sit side by side with their equivalence verified. The lesson: different outputs, same behavior.

### Typography
- Verilog code: JetBrains Mono, 11px, syntax-colored (see above)
- "Synthesis": Inter, 11px, `#4A90D9` at 0.5
- "Same input": Inter, 12px, `#64748B` at 0.4
- "Functionally equivalent": Inter, 12px, `#5AAA6E` at 0.6

### Easing
- Schematic dissolve: `easeIn(quad)` over 30 frames
- Code typing: `linear`, 2 frames per character
- Arrow draw: `easeInOut(cubic)` over 20 frames
- Netlist gates draw: `easeOut(quad)`, staggered 3 frames apart
- Checkmark pop: `easeOut(back(1.5))` scale from 0 to 1, 12 frames
- Equivalence label: `easeOut(quad)` over 15 frames

## Narration Sync
> "So in 1985, they moved up — from schematics to Verilog. A hardware description language. You described what you wanted the chip to do, and a synthesis tool generated the gates."
> "Now — synthesis was non-deterministic. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time."

Segment: `part2_007`

- **9:25** ("So in 1985, they moved up"): Schematic dissolves, Verilog code appears
- **9:30** ("a synthesis tool generated the gates"): Compiler processes, netlist flows out
- **9:35** ("synthesis was non-deterministic"): Triple-column layout appears
- **9:39** ("Run it twice, get different gates"): Three different netlists complete
- **9:42** ("The output varied every single time"): Green checkmarks — functionally equivalent

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <CircuitGrid spacing={20} color="#1E293B" opacity={0.03} />

    {/* Phase 1: Schematic dissolves → Verilog appears */}
    <Sequence from={0} durationInFrames={180}>
      {/* Dissolving schematic */}
      <Sequence from={0} durationInFrames={40}>
        <ParticleDissolve position={[960, 300]} size={[600, 300]}>
          <HandDrawnSchematic color="#64748B" opacity={0.5} />
        </ParticleDissolve>
      </Sequence>

      {/* Verilog code block */}
      <Sequence from={40}>
        <CodeBlock
          code={verilogCode} language="verilog"
          position={[960, 250]} width={500} height={200}
          bgColor="#1E293B" bgOpacity={0.3}
          font="JetBrains Mono" size={11}
          typeEffect charDelay={2}
        />
      </Sequence>

      {/* Compiler + netlist */}
      <Sequence from={90}>
        <FlowArrow from={[960, 360]} to={[960, 480]}
          color="#475569" opacity={0.3} drawDuration={15} />
        <CompilerIcon position={[960, 480]} size={60}
          color="#4A90D9" opacity={0.6}
          label="Synthesis" pulseOnLoad />
        <FlowArrow from={[960, 510]} to={[960, 560]}
          color="#475569" opacity={0.3} drawDuration={15} />
      </Sequence>

      <Sequence from={130}>
        <GateNetlist position={[960, 650]} width={400} height={200}
          gateCount={6} layout="horizontal"
          gateColor="#94A3B8" wireColor="#475569"
          drawDuration={40} />
      </Sequence>
    </Sequence>

    {/* Phase 2: Triple synthesis */}
    <Sequence from={180}>
      {/* Shared code at top */}
      <CodeBlock
        code={verilogCode} language="verilog"
        position={[960, 100]} width={800} height={140}
        bgColor="#1E293B" bgOpacity={0.3}
        font="JetBrains Mono" size={10}
      />
      <Label text="Same input" color="#64748B"
        opacity={0.4} position={[960, 25]} size={12} />

      {/* Three columns with arrows + compilers */}
      <Sequence from={40}>
        {[280, 960, 1640].map((x, i) => (
          <FlowArrow key={i} from={[x, 180]} to={[x, 420]}
            color="#475569" opacity={0.3}
            drawDuration={20} midIcon="gear" />
        ))}
      </Sequence>

      {/* Three different netlists */}
      <Sequence from={100}>
        <GateNetlist position={[280, 550]} width={400} height={250}
          gateCount={6} layout="horizontal_compact"
          gateColor="#94A3B8" wireColor="#475569"
          drawDuration={60} />
        <GateNetlist position={[960, 550]} width={400} height={250}
          gateCount={8} layout="vertical_long"
          gateColor="#94A3B8" wireColor="#475569"
          drawDuration={60} />
        <GateNetlist position={[1640, 550]} width={400} height={250}
          gateCount={5} layout="mixed_optimized"
          gateColor="#94A3B8" wireColor="#475569"
          drawDuration={60} />
      </Sequence>

      {/* Equivalence checkmarks */}
      <Sequence from={220}>
        {[280, 960, 1640].map((x, i) => (
          <Checkmark key={i} position={[x, 420]} size={30}
            color="#5AAA6E" popIn delay={i * 8} />
        ))}
        <Label text="Functionally equivalent" color="#5AAA6E"
          opacity={0.6} position={[960, 400]} size={12} />
        <DashedLine from={[280, 420]} to={[1640, 420]}
          color="#5AAA6E" opacity={0.2} drawDuration={20} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "verilog_synthesis_triple",
  "phases": [
    {
      "name": "schematic_to_verilog",
      "frames": [0, 180],
      "elements": ["dissolving_schematic", "verilog_code", "compiler", "single_netlist"]
    },
    {
      "name": "triple_synthesis",
      "frames": [180, 540],
      "elements": ["shared_code", "three_compilers", "three_netlists", "equivalence_checkmarks"]
    }
  ],
  "verilogCode": "module counter(\n  input clk, rst,\n  output reg [7:0] count\n);\n  always @(posedge clk)\n    if (rst) count <= 0;\n    else count <= count + 1;\nendmodule",
  "netlists": [
    { "id": "netlist_a", "gateCount": 6, "layout": "horizontal_compact" },
    { "id": "netlist_b", "gateCount": 8, "layout": "vertical_long" },
    { "id": "netlist_c", "gateCount": 5, "layout": "mixed_optimized" }
  ],
  "equivalence": true,
  "colors": {
    "code_keywords": "#C792EA",
    "code_text": "#E2E8F0",
    "compiler": "#4A90D9",
    "gates": "#94A3B8",
    "checkmark": "#5AAA6E"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part2_007"]
}
```

---
