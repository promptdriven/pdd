[Remotion]

# Section 2.13: Triple Synthesis — Non-Deterministic but Equivalent

**Tool:** Remotion
**Duration:** ~25s (750 frames @ 30fps)
**Timestamp:** 2:22 - 2:47

## Visual Description

The same Verilog code block runs through synthesis three times. Three visibly different gate-level netlists appear side by side — different shapes, different wiring, different layouts. They look nothing alike. Then a green checkmark appears over each one with the label "Functionally equivalent." The visual makes the core point: the output varies every time, but the behavior is identical. This is the insight that unlocks everything.

The three netlists are shown as stylized circuit diagrams in columns: different gate arrangements, different wire routing, but all producing the same truth table. The equivalence is proven, not assumed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: None — clean dark background

### Chart/Visual Elements

#### Source Code (top, centered)
- Compact Verilog code block: `#1E293B` background, JetBrains Mono 14px
- Position: centered, y: 80, width: 600px, height: 120px
- 3 arrows pointing down from code to each netlist column

#### Three Netlist Columns
- Column 1 (x: 200): Gate diagram A — `#E2E8F0` wires, `#78909C` gates, dense left-heavy layout
- Column 2 (x: 660): Gate diagram B — same colors, tree-like branching layout
- Column 3 (x: 1120): Gate diagram C — same colors, linear chain layout
- Each column: 400px wide, 500px tall, starting at y: 280
- All three visually distinct — different topologies

#### "Run N" Labels
- "Run 1", "Run 2", "Run 3": Inter, 14px, `#64748B`, centered above each column

#### Equivalence Checkmarks
- Large green checkmark: `#5AAA6E`, 48px, centered over each column
- Label: "Functionally equivalent", Inter, 16px, `#5AAA6E`, below each checkmark

### Animation Sequence
1. **Frame 0-60 (0-2s):** Verilog code block visible (from previous scene). Three arrows draw downward.
2. **Frame 60-120 (2-4s):** "Run 1" label appears. Netlist A generates top-to-bottom, wires connecting, gates appearing. Dense, left-heavy.
3. **Frame 120-180 (4-6s):** "Run 2" label appears. Netlist B generates — visibly different topology. Tree-like.
4. **Frame 180-240 (6-8s):** "Run 3" label appears. Netlist C generates — different again. Linear chain.
5. **Frame 240-300 (8-10s):** All three complete. Hold. The differences are obvious.
6. **Frame 300-420 (10-14s):** Green checkmarks animate in over each column simultaneously. Scale-up with bounce. "Functionally equivalent" labels fade in.
7. **Frame 420-600 (14-20s):** Hold. The three different-looking netlists all verified equivalent.
8. **Frame 600-750 (20-25s):** Columns fade. The equivalence message persists and transitions to the Synopsys/PDD overlay.

### Typography
- Code: JetBrains Mono, 14px, syntax-highlighted
- Run labels: Inter, 14px, regular (400), `#64748B`
- Checkmark label: Inter, 16px, semi-bold (600), `#5AAA6E`

### Easing
- Arrow draw: `easeInOut(cubic)` over 20 frames
- Netlist generation: `easeOut(quad)` — elements appear top-to-bottom
- Checkmark appear: `easeOut(back)` with overshoot 1.2
- Label fade-in: `easeOut(quad)` over 20 frames
- Column fade-out: `easeIn(quad)` over 60 frames

## Narration Sync
> "Now — synthesis was non-deterministic. Run it twice, get different gates. Different wiring. Different layout. The output varied every single time."
> "What Synopsys did was wrap a verification toolchain around the generator. Formal equivalence checking — using SAT and SMT solvers to produce mathematical proof that the output, whatever it looked like, behaved identically to the spec."

Segments: `part2_paradigm_shift_012`, `part2_paradigm_shift_013`

- **142.44s** (seg 012): Arrows draw — "synthesis was non-deterministic"
- **145.0s**: First netlist generates — "Run it twice, get different gates"
- **148.0s**: Second netlist generates — "Different wiring"
- **151.0s**: Third netlist generates — "Different layout"
- **153.92s** (seg 012 ends): All three visible, hold
- **154.10s** (seg 013): Checkmarks begin — "verification toolchain"
- **162.0s**: All checkmarks visible — "mathematical proof"
- **170.0s**: "behaved identically to the spec" — hold on equivalence
- **179.30s** (seg 013 ends): Fade transition begins

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={750}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Source code (persistent from prev) */}
    <CodeBlock
      language="verilog" code={verilogExample}
      font="JetBrains Mono" size={14}
      background="#1E293B" x={660} y={80} width={600}
    />

    {/* Three arrows */}
    <Sequence from={0}>
      <DrawArrows
        from={[960, 200]}
        to={[[200, 280], [660, 280], [1120, 280]]}
        color="#64748B" drawDuration={20}
      />
    </Sequence>

    {/* Netlist columns */}
    <Sequence from={60}>
      <NetlistColumn topology="dense-left" x={200} y={280}
        wireColor="#E2E8F0" gateColor="#78909C"
        generateDuration={60} label="Run 1" />
    </Sequence>
    <Sequence from={120}>
      <NetlistColumn topology="tree-branch" x={660} y={280}
        wireColor="#E2E8F0" gateColor="#78909C"
        generateDuration={60} label="Run 2" />
    </Sequence>
    <Sequence from={180}>
      <NetlistColumn topology="linear-chain" x={1120} y={280}
        wireColor="#E2E8F0" gateColor="#78909C"
        generateDuration={60} label="Run 3" />
    </Sequence>

    {/* Equivalence checkmarks */}
    <Sequence from={300}>
      {[200, 660, 1120].map(x => (
        <BounceIn key={x} duration={20} overshoot={1.2}>
          <Checkmark color="#5AAA6E" size={48} x={x} y={750} />
          <FadeIn duration={20}>
            <Text text="Functionally equivalent"
              font="Inter" size={16} weight={600}
              color="#5AAA6E" x={x} y={810} align="center" />
          </FadeIn>
        </BounceIn>
      ))}
    </Sequence>

    {/* Fade out */}
    <Sequence from={600}>
      <FadeOut duration={60} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "equivalence_demo",
  "chartId": "triple_synthesis_equivalence",
  "runs": [
    { "id": "run_1", "topology": "dense-left", "label": "Run 1" },
    { "id": "run_2", "topology": "tree-branch", "label": "Run 2" },
    { "id": "run_3", "topology": "linear-chain", "label": "Run 3" }
  ],
  "equivalenceLabel": "Functionally equivalent",
  "equivalenceColor": "#5AAA6E",
  "narrationSegments": ["part2_paradigm_shift_012", "part2_paradigm_shift_013"]
}
```

---
