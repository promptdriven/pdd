[Remotion]

# Section 2.10: Verilog Synthesis — Three Different Netlists

**Tool:** Remotion
**Duration:** ~36s (1080 frames @ 30fps)
**Timestamp:** 1:57 - 2:33

## Visual Description

A three-phase animated sequence showing the chip design paradigm shift:

**Phase 1 — Schematic dissolves to Verilog (0-8s):** A dense hand-drawn schematic (rendered as a tangle of lines, transistor symbols, and nodes) dissolves into clean Verilog code. The code appears line by line in a dark code editor — syntax highlighted in the style of a modern IDE but with period-appropriate HDL. Below the code, a Synopsys Design Compiler icon (a stylized gear + chip symbol) processes the code, and a gate-level netlist flows out from the right side — an abstract graph of nodes and connections.

**Phase 2 — Triple synthesis (8-23s):** The same Verilog code block is shown three times side by side (tiled across the frame). Below each, a "Synthesize" animation runs: the Synopsys gear spins, and three visibly different gate-level netlists generate below — different node arrangements, different wire routes, different layouts. All three are clearly distinct structures.

**Phase 3 — Equivalence verification (23-36s):** A green checkmark (`✓ Functionally equivalent`) animates over each of the three netlists simultaneously. Despite looking completely different, all three produce identical behavior. The checkmarks glow and pulse.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: None (code editor aesthetic)

### Chart/Visual Elements

#### Hand-Drawn Schematic (Phase 1, dissolves)
- Abstract representation: random-walk lines (`#94A3B8` at 0.4, 1px) connecting node dots (`#94A3B8`, 4px circles)
- Transistor symbols: small triangle-gate shapes scattered, `#94A3B8` at 0.5
- Fills area 400x600 centered, then dissolves (particle effect)

#### Verilog Code Block
- Editor frame: rounded rectangle, `#1E1E2E` fill, `#334155` 1px border
- Code font: JetBrains Mono, 14px
- Syntax colors: keywords `#C678DD` (purple), signals `#61AFEF` (blue), values `#E5C07B` (amber), comments `#5C6370` (grey)
- Sample code:
  ```
  module counter (
    input  clk, reset,
    output [7:0] count
  );
    reg [7:0] count_reg;
    always @(posedge clk)
      if (reset) count_reg <= 0;
      else count_reg <= count_reg + 1;
    assign count = count_reg;
  endmodule
  ```

#### Synopsys Processing Icon
- Stylized gear: `#4A90D9`, 40px, with small chip outline inside
- Spin animation during synthesis
- Arrow from code → gear → netlist

#### Gate-Level Netlists (x3)
- Abstract graph visualization: nodes (circles, 6px, `#10B981`) connected by edges (lines, 1px, `#10B981` at 0.4)
- Each netlist has a different random layout (same node count, different positions/routing)
- Netlist 1: clustered layout, ~30 nodes
- Netlist 2: grid-like layout, ~30 nodes
- Netlist 3: radial layout, ~30 nodes

#### Equivalence Checkmarks
- Green checkmark: `#10B981`, 48px, drawn with stroke animation
- Label: "Functionally equivalent" — Inter, 16px, `#10B981`, below checkmark
- Glow: `#10B981` at 0.15, 12px blur

### Animation Sequence
1. **Frame 0-60 (0-2s):** Hand-drawn schematic visible, dense and messy.
2. **Frame 60-120 (2-4s):** Schematic dissolves into particles. Particles reorganize.
3. **Frame 120-180 (4-6s):** Verilog code appears line by line in editor frame.
4. **Frame 180-240 (6-8s):** Synopsys gear appears below code, spins. Arrow + first netlist flows out.
5. **Frame 240-360 (8-12s):** View transitions to triple layout. Three copies of Verilog code tile across top.
6. **Frame 360-480 (12-16s):** Three Synopsys gears spin simultaneously below each code block.
7. **Frame 480-690 (16-23s):** Three different netlists generate below — each drawing its own unique node/edge layout. Clearly different from each other.
8. **Frame 690-780 (23-26s):** Green checkmarks draw over each netlist with stroke animation.
9. **Frame 780-900 (26-30s):** "Functionally equivalent" labels fade in below each checkmark.
10. **Frame 900-1080 (30-36s):** Hold. Checkmarks pulse gently. Visual settles.

### Typography
- Verilog code: JetBrains Mono, 14px, syntax-highlighted
- Equivalence label: Inter, 16px, semi-bold, `#10B981`
- Netlist node labels: None (abstract)

### Easing
- Schematic dissolve: `easeIn(quad)` particle scatter over 60 frames
- Code line reveal: `easeOut(cubic)` per line, 8 frames each
- Gear spin: `linear` continuous, 2 rotations per synthesis
- Netlist draw: `easeInOut(cubic)` for node placement, `easeOut(quad)` for edge drawing
- Checkmark stroke: `easeOut(cubic)` over 30 frames
- Label fade-in: `easeOut(quad)` over 20 frames

## Narration Sync
> "In the 1980s, chip designers drew every gate by hand. When transistor counts hit tens of thousands, they couldn't keep up. So in 1985, they moved up — from schematics to Verilog. A hardware description language. You described what you wanted the chip to do, and a synthesis tool generated the gates."
> "Now — synthesis was non-deterministic. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time."

Segments: `part2_paradigm_shift_014`, `part2_paradigm_shift_015`

- **1:57** (117.12s): Schematic appears — "In the 1980s, chip designers drew every gate by hand"
- **2:07** (127s): Schematic dissolves to Verilog — "they moved up — from schematics to Verilog"
- **2:12** (132s): Synopsys processes code — "a synthesis tool generated the gates"
- **2:20** (139.84s): Triple layout — "synthesis was non-deterministic"
- **2:26** (146s): Three different netlists visible — "Different wiring. Different layout"
- **2:33** (152.82s): Checkmarks appear (transition to next spec)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={1080}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Phase 1: Schematic dissolve → Verilog */}
    <Sequence from={0} durationInFrames={240}>
      <SchematicDissolve startFrame={60} dissolveFrames={60} />
      <Sequence from={120}>
        <CodeBlockReveal
          code={verilogCode} language="verilog"
          font="JetBrains Mono" size={14}
          lineDelay={8}
        />
      </Sequence>
      <Sequence from={180}>
        <SynopsysGear x={960} y={700} size={40} color="#4A90D9" />
        <ArrowFlow from={[960, 650]} to={[1300, 700]} />
        <NetlistGraph layout="clustered" nodes={30} color="#10B981" />
      </Sequence>
    </Sequence>

    {/* Phase 2: Triple synthesis */}
    <Sequence from={240} durationInFrames={450}>
      <TripleLayout>
        {[0, 1, 2].map(i => (
          <Column key={i}>
            <CodeBlockMini code={verilogCode} />
            <Sequence from={120}>
              <SynopsysGear spinning />
            </Sequence>
            <Sequence from={240}>
              <NetlistGraph
                layout={['clustered', 'grid', 'radial'][i]}
                nodes={30} color="#10B981"
                drawDuration={210}
              />
            </Sequence>
          </Column>
        ))}
      </TripleLayout>
    </Sequence>

    {/* Phase 3: Equivalence checkmarks */}
    <Sequence from={690} durationInFrames={390}>
      <TripleLayout>
        {[0, 1, 2].map(i => (
          <Sequence key={i} from={0}>
            <StrokeCheckmark size={48} color="#10B981" drawFrames={30} />
            <Sequence from={90}>
              <FadeIn duration={20}>
                <Text text="Functionally equivalent"
                  font="Inter" size={16} color="#10B981" weight={600} />
              </FadeIn>
            </Sequence>
          </Sequence>
        ))}
      </TripleLayout>
    </Sequence>

  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_infographic",
  "phases": [
    {
      "id": "schematic_to_verilog",
      "description": "Hand-drawn schematic dissolves into Verilog code",
      "frames": [0, 240]
    },
    {
      "id": "triple_synthesis",
      "description": "Same Verilog synthesized three times, producing three different netlists",
      "frames": [240, 690],
      "netlists": ["clustered", "grid", "radial"]
    },
    {
      "id": "equivalence_check",
      "description": "Green checkmarks confirm all three are functionally equivalent",
      "frames": [690, 1080],
      "checkColor": "#10B981"
    }
  ],
  "narrationSegments": ["part2_paradigm_shift_014", "part2_paradigm_shift_015"]
}
```

---
