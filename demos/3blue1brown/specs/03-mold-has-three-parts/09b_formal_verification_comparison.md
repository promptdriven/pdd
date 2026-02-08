# Section 3.9b: Formal Verification Side-by-Side

**Tool:** Remotion
**Duration:** ~25 seconds
**Timestamp:** 13:20 - 13:45

## Visual Description

Side-by-side comparison expanding on the Z3/Synopsys sidebar. LEFT panel: "Synopsys Formality: SMT solver proves RTL = gates for all inputs." RIGHT panel: "PDD + Z3: SMT solver proves code satisfies spec for all inputs." Both panels share a common label at the bottom: "Mathematical proof, not testing." The visual reinforces that PDD's formal verification is not a metaphor for chip design verification -- it IS the same category of mathematical guarantee.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Vertical split at center, clean divider

### Animation Elements

1. **Left Panel: Synopsys Formality**
   - Header: "Synopsys Formality" in teal (#2AA198)
   - Chip/circuit icon or schematic fragment (callback to Part 2)
   - Core text: "SMT solver proves RTL = gates for all inputs"
   - "RTL = gates" rendered as a mathematical equivalence
   - "for all inputs" emphasized (italic or slight highlight)
   - Subtle circuit-board pattern in background at low opacity

2. **Right Panel: PDD + Z3**
   - Header: "PDD + Z3" in teal (#2AA198)
   - Code/prompt icon (callback to Part 3 mold structure)
   - Core text: "SMT solver proves code satisfies spec for all inputs"
   - "code satisfies spec" rendered as a mathematical satisfaction relation
   - "for all inputs" emphasized (matching left panel styling)
   - Subtle code-pattern in background at low opacity

3. **Center Divider**
   - Thin vertical line, teal (#2AA198) at 30% opacity
   - Separates but connects the two panels

4. **Shared Bottom Label**
   - Text: "Mathematical proof, not testing."
   - Spans full width, centered below both panels
   - Larger font, white (#FFFFFF), bold
   - Green verification checkmarks (#5AAA6E) flanking the text
   - Underline or subtle rule below for emphasis

5. **Mathematical Notation (Optional Enhancement)**
   - LEFT: "forall x in Inputs: Synth(RTL, x) == Impl(gates, x)"
   - RIGHT: "forall x in Inputs: Code(x) |= Spec(x)"
   - Rendered in mathematical typeset style (serif/italic)
   - Appears below the prose description as a formal statement

### Animation Sequence

1. **Frame 0-90 (0-3s):** Left panel builds
   - Teal divider line draws from center-top to center-bottom
   - Left panel header "Synopsys Formality" fades in
   - Circuit icon/fragment appears
   - Background pattern faintly visible

2. **Frame 90-180 (3-6s):** Left panel text
   - "SMT solver proves" fades in
   - "RTL = gates" appears as mathematical notation, brief glow
   - "for all inputs" appears, italicized
   - Left panel fully composed

3. **Frame 180-270 (6-9s):** Right panel builds
   - Right panel header "PDD + Z3" fades in
   - Code/prompt icon appears
   - Mirrors the left panel's timing and rhythm

4. **Frame 270-360 (9-12s):** Right panel text
   - "SMT solver proves" fades in (same words, visual parallel)
   - "code satisfies spec" appears, brief glow
   - "for all inputs" appears, matching left panel style
   - Viewer sees the parallel structure

5. **Frame 360-450 (12-15s):** Mathematical notation (optional)
   - LEFT: formal notation appears below prose
   - RIGHT: formal notation appears below prose
   - Both in serif/italic mathematical style
   - Reinforces the formal rigor

6. **Frame 450-540 (15-18s):** Shared label
   - "Mathematical proof, not testing." fades in at bottom
   - Green checkmarks (#5AAA6E) appear on either side
   - The word "not testing" draws a subtle strikethrough on an implied "testing" concept
   - Both panels glow slightly in unison

7. **Frame 540-750 (18-25s):** Hold for extended narration
   - Full composition held
   - Subtle breathing animation (very slight scale oscillation)
   - "Mathematical proof, not testing." gently pulses
   - Holds through narration about "reasoned symbolically over the entire space" and "the same technology"

### Visual Design: Side-by-Side Layout

```
+----------------------------+----------------------------+
|                            |                            |
|    SYNOPSYS FORMALITY      |        PDD + Z3            |
|    (teal header)           |     (teal header)          |
|                            |                            |
|    [circuit icon]          |    [code/prompt icon]      |
|                            |                            |
|    SMT solver proves       |    SMT solver proves       |
|    RTL = gates             |    code satisfies spec     |
|    for all inputs          |    for all inputs          |
|                            |                            |
|    forall x: Synth(RTL,x)  |    forall x: Code(x)      |
|    == Impl(gates,x)        |    |= Spec(x)             |
|                            |                            |
+----------------------------+----------------------------+
|                                                        |
|    checkmark  Mathematical proof, not testing.  checkmark |
|                                                        |
+--------------------------------------------------------+
  Teal accents (#2AA198)     Green checks (#5AAA6E)
  White bold bottom label    Muted math notation
```

### Code Structure (Remotion)

```typescript
const FormalVerificationComparison: React.FC = () => {
  const frame = useCurrentFrame();

  // Divider line draw
  const dividerHeight = interpolate(
    frame,
    [0, 60],
    [0, 100],
    { extrapolateRight: 'clamp' }
  );

  // Left panel
  const leftHeaderOpacity = interpolate(
    frame, [0, 45], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const leftTextOpacity = interpolate(
    frame, [90, 150], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Right panel
  const rightHeaderOpacity = interpolate(
    frame, [180, 225], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const rightTextOpacity = interpolate(
    frame, [270, 330], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Mathematical notation
  const mathOpacity = interpolate(
    frame, [360, 420], [0, 0.6],
    { extrapolateRight: 'clamp' }
  );

  // Shared bottom label
  const labelOpacity = interpolate(
    frame, [450, 510], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Gentle pulse on bottom label
  const labelPulse = frame > 510
    ? 1.0 + Math.sin((frame - 510) * 0.06) * 0.05
    : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Center divider */}
      <div style={{
        position: 'absolute',
        left: '50%',
        top: 80,
        width: 1,
        height: `${dividerHeight}%`,
        maxHeight: 700,
        backgroundColor: '#2AA198',
        opacity: 0.3,
      }} />

      {/* Left Panel: Synopsys Formality */}
      <div style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '50%',
        height: '100%',
        padding: '80px 60px',
      }}>
        <PanelHeader
          text="Synopsys Formality"
          color="#2AA198"
          opacity={leftHeaderOpacity}
        />
        <CircuitIcon
          opacity={leftHeaderOpacity}
          color="#2AA198"
        />
        <ProofDescription
          opacity={leftTextOpacity}
          prefix="SMT solver proves"
          relation="RTL ≡ gates"
          qualifier="for all inputs"
        />
        <MathNotation
          opacity={mathOpacity}
          formula="∀x ∈ Inputs: Synth(RTL, x) ≡ Impl(gates, x)"
        />
      </div>

      {/* Right Panel: PDD + Z3 */}
      <div style={{
        position: 'absolute',
        right: 0,
        top: 0,
        width: '50%',
        height: '100%',
        padding: '80px 60px',
      }}>
        <PanelHeader
          text="PDD + Z3"
          color="#2AA198"
          opacity={rightHeaderOpacity}
        />
        <CodePromptIcon
          opacity={rightHeaderOpacity}
          color="#2AA198"
        />
        <ProofDescription
          opacity={rightTextOpacity}
          prefix="SMT solver proves"
          relation="code satisfies spec"
          qualifier="for all inputs"
        />
        <MathNotation
          opacity={mathOpacity}
          formula="∀x ∈ Inputs: Code(x) ⊨ Spec(x)"
        />
      </div>

      {/* Shared bottom label */}
      <div style={{
        position: 'absolute',
        bottom: 100,
        width: '100%',
        textAlign: 'center',
        opacity: labelOpacity,
        transform: `scale(${labelPulse})`,
      }}>
        <div style={{
          display: 'flex',
          justifyContent: 'center',
          alignItems: 'center',
          gap: 20,
        }}>
          <Checkmark color="#5AAA6E" size={28} />
          <span style={{
            fontSize: 30,
            fontWeight: 700,
            color: '#FFFFFF',
            fontFamily: 'Inter, sans-serif',
          }}>
            Mathematical proof, not testing.
          </span>
          <Checkmark color="#5AAA6E" size={28} />
        </div>
      </div>
    </AbsoluteFill>
  );
};
```

### Proof Description Component

```typescript
const ProofDescription: React.FC<{
  opacity: number;
  prefix: string;
  relation: string;
  qualifier: string;
}> = ({ opacity, prefix, relation, qualifier }) => {
  return (
    <div style={{
      opacity,
      marginTop: 30,
      fontFamily: 'Inter, sans-serif',
    }}>
      <div style={{
        fontSize: 22,
        color: '#B0B0C0',
        marginBottom: 8,
      }}>
        {prefix}
      </div>
      <div style={{
        fontSize: 28,
        color: '#FFFFFF',
        fontWeight: 600,
        marginBottom: 8,
      }}>
        {relation}
      </div>
      <div style={{
        fontSize: 22,
        color: '#B0B0C0',
        fontStyle: 'italic',
      }}>
        {qualifier}
      </div>
    </div>
  );
};
```

### Math Notation Component

```typescript
const MathNotation: React.FC<{
  opacity: number;
  formula: string;
}> = ({ opacity, formula }) => {
  return (
    <div style={{
      opacity,
      marginTop: 24,
      fontSize: 18,
      fontFamily: 'CMU Serif, Georgia, serif',
      fontStyle: 'italic',
      color: '#8090A0',
      letterSpacing: 1,
    }}>
      {formula}
    </div>
  );
};
```

### Easing

- Divider line draw: `easeInOutQuad`
- Panel headers: `easeOutCubic`
- Text fade-ins: `easeOutCubic`
- Mathematical notation: `easeOutCubic`
- Bottom label: `easeOutCubic`
- Label pulse: Sinusoidal (manual Math.sin)

## Narration Sync

> "When Z3 proves that a function never returns null for any 32-bit integer input, it hasn't tried every input -- it's reasoned symbolically over the entire space. The same math. The same certainty. The same category of guarantee the semiconductor industry relies on for billion-dollar tapeouts."

> "Traditional unit tests are still samples -- and PDD uses those too. But Z3 gives you walls that are *proven*, not just tested. And in that sense, the chip design analogy isn't a metaphor. It's the same technology."

- "When Z3 proves" -- right panel fully visible, both sides established
- "reasoned symbolically over the entire space" -- "for all inputs" emphasized on both sides
- "The same math. The same certainty." -- bottom label pulses
- "isn't a metaphor. It's the same technology." -- full composition held, maximum impact

## Audio Notes

- Panel build sounds: soft structural tones (glass or metal, precise)
- Mathematical notation: subtle "pen on paper" sound
- "Mathematical proof, not testing." landing: authoritative, clean tone
- "The same technology" moment: brief resonant chord -- emotional weight
- Ambient throughout: low electronic hum suggesting computational precision

## Visual Style Notes

- The side-by-side parallel structure is THE key visual device -- the viewer should see the same words ("SMT solver proves ... for all inputs") on both sides and realize these are the same thing
- Teal (#2AA198) maintains the chip design visual language from Part 2
- The mathematical notation is optional but adds rigor for technical viewers; keep it at reduced opacity so it doesn't overwhelm non-technical viewers
- Green checkmarks (#5AAA6E) on the bottom label connect back to the test/verification color used throughout Part 3
- "Mathematical proof, not testing." is the thesis statement of this section -- it gets the most visual weight
- This section has extra narration time (25 seconds) because the narration covers two paragraphs; the hold time lets the composition breathe while the narrator delivers the "isn't a metaphor" punchline

## Transition

Hard cut back to the main mold visualization for Section 3.10 (injection nozzle), transitioning from the teal chip-design sidebar back to the amber/blue/green mold color palette. The teal sidebar visually closes.
