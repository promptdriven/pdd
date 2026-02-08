# Section 2.9d: Three Netlists (Non-Deterministic Synthesis)

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 9:10 - 9:30

## Visual Description

Same Verilog code runs through synthesis three times. Three visibly different gate-level netlists appear side by side. All different. Then a green checkmark appears over each: "Functionally equivalent." This demonstrates the core insight: non-deterministic generation can be verified deterministically.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continues from Section 2.9c's pipeline view

### Visual Elements

1. **Verilog Code Block (Source)**
   - Same code from Section 2.9c, positioned top-center
   - Teal (#2AA198) syntax highlighting
   - Dark code background (#1E1E2E)
   - Stable, unchanged -- the specification
   - Subtle blue-ish glow to suggest it holds the value

2. **Three Synthesis Runs**
   - Same compiler icon appears three times (or one icon runs three times)
   - Each run produces a different output
   - Visual indicator: "Run 1", "Run 2", "Run 3" labels

3. **Three Gate-Level Netlists**
   - Side by side in the lower two-thirds of screen
   - Each uses different gate arrangements and wiring
   - Darker teal (#1A7A6E) for all three
   - Visibly, obviously different from each other
   - All machine-generated (precise, uniform, but different layouts)

4. **Green Checkmarks**
   - Appear over each netlist simultaneously
   - Verification green (#5AAA6E)
   - Label beneath or beside: "Functionally Equivalent"
   - Represents formal equivalence checking

### Visual Layout

```
┌─────────────────────────────────────────────────┐
│                                                 │
│          ┌─────────────────────┐                │
│          │  module alu(...)    │                │
│          │    always @(*)     │  VERILOG        │
│          │      case(op)     │  (same input)   │
│          │    ...            │                │
│          └─────────────────────┘                │
│            │         │         │                │
│         Run 1     Run 2     Run 3               │
│            │         │         │                │
│            ▼         ▼         ▼                │
│  ┌──────────┐ ┌──────────┐ ┌──────────┐        │
│  │ ┌┐  ┌┐  │ │  ┌┐ ┌┐  │ │┌┐   ┌┐  │        │
│  │ │&│─│|│  │ │  │!│─│&│  │ ││|│──│!│  │        │
│  │ └┘  └┘  │ │  └┘ └┘  │ │└┘   └┘  │        │
│  │   ┌┐    │ │ ┌┐  ┌┐  │ │  ┌┐ ┌┐  │        │
│  │   │!│   │ │ │|│──│!│  │ │  │&│─│|│  │        │
│  │   └┘    │ │ └┘  └┘  │ │  └┘ └┘  │        │
│  └──────────┘ └──────────┘ └──────────┘        │
│       ✓            ✓            ✓               │
│         "Functionally Equivalent"               │
│                                                 │
└─────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Setup from previous section
   - Verilog code visible at top, centered
   - Previous single netlist fades or slides away
   - Three empty slots appear below

2. **Frame 60-150 (2-5s):** First synthesis run
   - Arrow/flow from code to left slot
   - "Run 1" label appears
   - Synthesis processing animation (brief)
   - First netlist draws itself in the left position
   - Gate symbols and wiring appear: Layout A

3. **Frame 150-240 (5-8s):** Second synthesis run
   - Arrow/flow from same code to center slot
   - "Run 2" label appears
   - Synthesis processing animation (brief)
   - Second netlist draws itself in the center position
   - Visibly different arrangement: Layout B
   - Different gate ordering, different wire routing

4. **Frame 240-330 (8-11s):** Third synthesis run
   - Arrow/flow from same code to right slot
   - "Run 3" label appears
   - Synthesis processing animation (brief)
   - Third netlist draws itself in the right position
   - Again visibly different: Layout C
   - Third unique arrangement

5. **Frame 330-420 (11-14s):** All three visible, differences highlighted
   - Brief hold: three different netlists from one source
   - Optional: subtle pulsing on the differences
   - Tension: these look different -- is that a problem?

6. **Frame 420-510 (14-17s):** Verification checkmarks appear
   - Green checkmark (#5AAA6E) appears over Netlist 1
   - Then over Netlist 2 (0.5s delay)
   - Then over Netlist 3 (0.5s delay)
   - Satisfying sequential appearance
   - Each checkmark accompanied by subtle animation (scale bounce)

7. **Frame 510-600 (17-20s):** "Functionally Equivalent" label
   - Text fades in below all three netlists
   - "Functionally Equivalent" in green (#5AAA6E)
   - Connecting line or bracket groups all three
   - Hold: the insight lands

### Gate-Level Netlist Variations

Each netlist should be visibly different while representing the same function:

**Netlist A (Left):**
- AND gates first, then OR gates
- Linear left-to-right flow
- Compact, tightly packed

**Netlist B (Center):**
- OR gates first, then AND gates
- Tree-like branching structure
- More spread out vertically

**Netlist C (Right):**
- Mixed gate ordering
- Diagonal wiring pattern
- Uses NAND/NOR equivalents (different gates, same function)

### Checkmark Animation

```typescript
const VerificationCheckmark = ({ delay, position }) => {
  const frame = useCurrentFrame();
  const adjustedFrame = frame - delay;

  if (adjustedFrame < 0) return null;

  const scale = spring({
    frame: adjustedFrame,
    fps: 30,
    config: {
      damping: 12,
      stiffness: 200,
      mass: 0.5,
    },
  });

  const opacity = interpolate(adjustedFrame, [0, 10], [0, 1], {
    extrapolateRight: 'clamp',
  });

  return (
    <div style={{
      position: 'absolute',
      ...position,
      transform: `scale(${scale})`,
      opacity,
    }}>
      <svg width={60} height={60} viewBox="0 0 60 60">
        <circle cx={30} cy={30} r={28} fill="none" stroke="#5AAA6E" strokeWidth={3} />
        <path
          d="M18 30 L26 38 L42 22"
          fill="none"
          stroke="#5AAA6E"
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />
      </svg>
    </div>
  );
};
```

### Netlist Component

```typescript
const GateNetlist = ({ variant, drawProgress, position }) => {
  // Each variant has a different gate layout
  const layouts = {
    A: [
      { type: 'AND', x: 20, y: 20 },
      { type: 'AND', x: 20, y: 60 },
      { type: 'OR', x: 80, y: 40 },
      { type: 'NOT', x: 120, y: 40 },
    ],
    B: [
      { type: 'OR', x: 20, y: 40 },
      { type: 'NOT', x: 60, y: 20 },
      { type: 'AND', x: 60, y: 60 },
      { type: 'OR', x: 100, y: 40 },
    ],
    C: [
      { type: 'NAND', x: 30, y: 20 },
      { type: 'NOR', x: 30, y: 60 },
      { type: 'AND', x: 90, y: 30 },
      { type: 'NOT', x: 90, y: 60 },
    ],
  };

  const gates = layouts[variant];
  const visibleGates = Math.floor(drawProgress * gates.length);

  return (
    <div style={{
      position: 'absolute',
      ...position,
      width: 280,
      height: 180,
      border: '1px solid rgba(42, 161, 152, 0.3)',
      borderRadius: 8,
      backgroundColor: 'rgba(26, 122, 110, 0.08)',
    }}>
      <svg width={280} height={180}>
        {gates.slice(0, visibleGates).map((gate, i) => (
          <GateSymbol key={i} type={gate.type} x={gate.x} y={gate.y} color="#1A7A6E" />
        ))}
        <WireConnections gates={gates.slice(0, visibleGates)} color="#1A7A6E" />
      </svg>
      <div style={{
        position: 'absolute',
        bottom: -24,
        width: '100%',
        textAlign: 'center',
        fontFamily: 'JetBrains Mono',
        fontSize: 12,
        color: '#8A9BA8',
      }}>
        Run {variant === 'A' ? '1' : variant === 'B' ? '2' : '3'}
      </div>
    </div>
  );
};
```

### Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={600}>
  {/* Verilog source code (persistent at top) */}
  <VerilogCode progress={1} compact={true} position="top-center" />

  {/* Three synthesis runs, staggered */}
  <Sequence from={60} durationInFrames={90}>
    <SynthesisArrow target="left" />
    <GateNetlist variant="A" drawProgress={netlistAProgress} position={leftPos} />
  </Sequence>

  <Sequence from={150} durationInFrames={90}>
    <SynthesisArrow target="center" />
    <GateNetlist variant="B" drawProgress={netlistBProgress} position={centerPos} />
  </Sequence>

  <Sequence from={240} durationInFrames={90}>
    <SynthesisArrow target="right" />
    <GateNetlist variant="C" drawProgress={netlistCProgress} position={rightPos} />
  </Sequence>

  {/* Verification checkmarks */}
  <Sequence from={420}>
    <VerificationCheckmark delay={0} position={checkPos1} />
    <VerificationCheckmark delay={15} position={checkPos2} />
    <VerificationCheckmark delay={30} position={checkPos3} />
  </Sequence>

  {/* "Functionally Equivalent" label */}
  <Sequence from={510}>
    <FadeIn durationInFrames={30}>
      <EquivalenceLabel
        text="Functionally Equivalent"
        color="#5AAA6E"
        fontFamily="JetBrains Mono"
        fontSize={22}
        position="bottom-center"
      />
    </FadeIn>
  </Sequence>
</Sequence>
```

### Easing

- Netlist drawing: `easeInOutCubic` (smooth reveal)
- Checkmark appearance: `spring` (bouncy, satisfying)
- Label fade-in: `easeOutCubic`
- Synthesis arrows: `easeOutQuad`

## Narration Sync

> "What Synopsys did was wrap a verification toolchain around the generator. Formal equivalence checking--using SAT and SMT solvers to produce mathematical proof that the output, whatever it looked like, behaved identically to the spec. The gates were different every time. The function was the same every time."

Key sync points:
- "verification toolchain" -- checkmarks begin appearing
- "formal equivalence checking" -- checkmarks over all three netlists
- "mathematical proof" -- "Functionally Equivalent" label visible
- "gates were different every time" -- audience sees three different netlists
- "function was the same every time" -- green checkmarks confirm equivalence

## Audio Notes

- Each netlist drawing: Subtle digital/electronic construction sound
- Each checkmark: Satisfying "ding" or confirmation tone (ascending pitch: ding, ding, ding)
- "Functionally Equivalent" label: Subtle harmonic resolution
- Music: Resolving chord -- the solution to non-determinism

## Visual Style Notes

- This is the "aha" moment for the chip design analogy
- Three different outputs from the same input is visually striking
- The checkmarks provide emotional resolution: different is OK
- Green checkmarks should feel earned and satisfying
- Directly parallels PDD: LLM generates different code each time, but tests verify equivalence
- 3Blue1Brown aesthetic: clean, mathematical proof visualized
- The Verilog code at top should feel stable/permanent vs. the varying netlists below
- Subtle glow on Verilog code (value lives here) vs. no glow on netlists (just output)

## Transition

Holds on the three-netlist view, then Section 2.9e pulls back to show the abstraction timeline that contextualizes this shift historically.
