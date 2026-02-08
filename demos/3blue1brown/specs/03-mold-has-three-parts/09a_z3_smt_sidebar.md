# Section 3.9a: Z3 / SMT Solver Sidebar

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 13:00 - 13:20

## Visual Description

Brief sidebar that visually calls back to Part 2's chip design sequence. The Synopsys Formality logo/icon from Part 2 (Section 2.10) reappears on the left alongside the Z3 logo on the right. Both are rendered in teal (#2AA198) to maintain the chip design visual language. Text appears between them: "Hardware: SMT-based formal proof. PDD: SMT-based formal proof. Same math." This establishes that PDD's verification is not an analogy -- it is literally the same class of mathematical technology.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Clean, centered layout -- sidebar feel (slightly different framing from main flow)

### Animation Elements

1. **Synopsys Formality Icon (Left)**
   - Reuses the Synopsys checkmark/logo visual from Part 2 Section 2.10
   - Teal color (#2AA198) -- chip design visual language
   - Positioned left-center
   - Fades in with recognition callback ("you've seen this before")
   - Label below: "Synopsys Formality"

2. **Z3 Logo (Right)**
   - Z3 solver logo or stylized "Z3" text
   - Teal color (#2AA198) -- same family of technology
   - Positioned right-center, mirroring Synopsys
   - Label below: "Z3 (Microsoft Research)"

3. **Connecting Element**
   - Horizontal line or bridge between the two logos
   - Teal, subtle glow
   - Appears after both logos are visible
   - Suggests equivalence/shared heritage

4. **Comparison Text Block**
   - Three lines centered below the logos:
     - "Hardware: SMT-based formal proof"
     - "PDD: SMT-based formal proof"
     - "Same math."
   - First two lines in muted white (#B0B0C0)
   - "Same math." in brighter white (#FFFFFF), bold, slightly larger
   - Text appears sequentially, line by line

5. **Sidebar Frame (Optional)**
   - Subtle border or slight background shift to signal "sidebar" context
   - Thin teal border at top and bottom, or slight vignette
   - Differentiates this from the main flow visually

### Animation Sequence

1. **Frame 0-60 (0-2s):** Synopsys callback
   - Synopsys Formality icon fades in from left
   - Brief shimmer/pulse -- "you remember this from Part 2"
   - Teal glow establishes
   - Label "Synopsys Formality" fades in below

2. **Frame 60-120 (2-4s):** Z3 appears
   - Z3 logo fades in from right
   - Mirrors the Synopsys positioning
   - Same teal color -- immediately signals shared category
   - Label "Z3 (Microsoft Research)" fades in below

3. **Frame 120-180 (4-6s):** Connection established
   - Horizontal bridge line draws between the two logos
   - Both logos pulse gently in unison
   - An equals sign or "~" appears at the center of the bridge

4. **Frame 180-300 (6-10s):** Text appears line by line
   - Frame 180-220: "Hardware: SMT-based formal proof" fades in
   - Frame 220-260: "PDD: SMT-based formal proof" fades in below
   - Frame 260-300: "Same math." fades in, larger and bolder
   - Each line appears with slight stagger for readability

5. **Frame 300-420 (10-14s):** Hold and emphasize
   - "Same math." pulses gently
   - Both logos hold steady
   - Bridge line glows
   - Full composition visible

6. **Frame 420-600 (14-20s):** Hold for narration completion
   - Stable composition
   - "Same math." continues gentle pulse
   - Holds until narration about "mathematical proof that a property holds for every possible input"

### Visual Design: Sidebar Layout

```
+----------------------------------------------------------+
|  _______________  thin teal accent line  _______________  |
|                                                          |
|                                                          |
|     [Synopsys]  ========= ~ =========  [Z3 Logo]        |
|     Formality        (bridge)        (Microsoft          |
|                                       Research)          |
|                                                          |
|          Hardware: SMT-based formal proof                 |
|          PDD: SMT-based formal proof                     |
|                  Same math.                              |
|                                                          |
|                                                          |
|  _______________  thin teal accent line  _______________  |
+----------------------------------------------------------+
  All teal (#2AA198)              "Same math." bold white
```

### Code Structure (Remotion)

```typescript
const Z3SmtSidebar: React.FC = () => {
  const frame = useCurrentFrame();

  // Synopsys icon fade-in
  const synopsysOpacity = interpolate(
    frame,
    [0, 45],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Z3 icon fade-in
  const z3Opacity = interpolate(
    frame,
    [60, 105],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Bridge line draw progress (0 to 1)
  const bridgeProgress = interpolate(
    frame,
    [120, 180],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Text lines staggered
  const line1Opacity = interpolate(
    frame, [180, 220], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const line2Opacity = interpolate(
    frame, [220, 260], [0, 1],
    { extrapolateRight: 'clamp' }
  );
  const line3Opacity = interpolate(
    frame, [260, 300], [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // "Same math." pulse
  const sameMathPulse = frame > 300
    ? 1.0 + Math.sin((frame - 300) * 0.08) * 0.1
    : 1.0;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Sidebar accent lines */}
      <SidebarFrame color="#2AA198" opacity={0.3} />

      {/* Logo row */}
      <div style={{
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        gap: 200,
        marginTop: 280,
      }}>
        {/* Synopsys Formality */}
        <div style={{ opacity: synopsysOpacity, textAlign: 'center' }}>
          <SynopsysIcon color="#2AA198" size={100} />
          <div style={{
            marginTop: 16,
            fontSize: 16,
            color: '#2AA198',
            fontFamily: 'Inter, sans-serif',
          }}>
            Synopsys Formality
          </div>
        </div>

        {/* Bridge line */}
        <BridgeLine
          progress={bridgeProgress}
          color="#2AA198"
          width={200}
        />

        {/* Z3 */}
        <div style={{ opacity: z3Opacity, textAlign: 'center' }}>
          <Z3Icon color="#2AA198" size={100} />
          <div style={{
            marginTop: 16,
            fontSize: 16,
            color: '#2AA198',
            fontFamily: 'Inter, sans-serif',
          }}>
            Z3 (Microsoft Research)
          </div>
        </div>
      </div>

      {/* Comparison text */}
      <div style={{
        position: 'absolute',
        bottom: 280,
        width: '100%',
        textAlign: 'center',
      }}>
        <div style={{
          fontSize: 24,
          color: '#B0B0C0',
          opacity: line1Opacity,
          fontFamily: 'Inter, sans-serif',
          marginBottom: 12,
        }}>
          Hardware: SMT-based formal proof
        </div>
        <div style={{
          fontSize: 24,
          color: '#B0B0C0',
          opacity: line2Opacity,
          fontFamily: 'Inter, sans-serif',
          marginBottom: 20,
        }}>
          PDD: SMT-based formal proof
        </div>
        <div style={{
          fontSize: 32,
          color: '#FFFFFF',
          opacity: line3Opacity,
          fontWeight: 700,
          fontFamily: 'Inter, sans-serif',
          transform: `scale(${sameMathPulse})`,
        }}>
          Same math.
        </div>
      </div>
    </AbsoluteFill>
  );
};
```

### Bridge Line Component

```typescript
const BridgeLine: React.FC<{
  progress: number;
  color: string;
  width: number;
}> = ({ progress, color, width }) => {
  return (
    <div style={{
      position: 'relative',
      width,
      height: 2,
    }}>
      {/* Line */}
      <div style={{
        width: `${progress * 100}%`,
        height: 2,
        backgroundColor: color,
        boxShadow: `0 0 8px ${color}`,
      }} />
      {/* Center equivalence symbol */}
      {progress > 0.5 && (
        <div style={{
          position: 'absolute',
          top: -14,
          left: '50%',
          transform: 'translateX(-50%)',
          fontSize: 20,
          color,
          opacity: (progress - 0.5) * 2,
        }}>
          =
        </div>
      )}
    </div>
  );
};
```

### Easing

- Logo fade-ins: `easeOutCubic`
- Bridge line draw: `easeInOutQuad`
- Text line fade-ins: `easeOutCubic`
- "Same math." pulse: Sinusoidal (manual Math.sin)
- Sidebar frame: `easeOutCubic`

## Narration Sync

> "Now -- here's something most people don't know. In chip design, Synopsys Formality uses SAT and SMT solvers to mathematically prove equivalence. PDD uses Z3 -- the same class of SMT solver -- to formally verify properties of generated code. Not sampling. Not 'run a bunch of inputs and hope.' Mathematical proof that a property holds for *every possible input*."

- "Synopsys Formality" -- Synopsys icon visible, recognizable from Part 2
- "PDD uses Z3" -- Z3 icon appears
- "the same class of SMT solver" -- bridge line draws, connecting the two
- "Hardware: SMT-based formal proof" -- first text line
- "PDD: SMT-based formal proof" -- second text line
- "Mathematical proof" -- "Same math." appears and pulses

## Audio Notes

- Callback sound: brief echo of the teal/chip-design motif from Part 2
- Soft "connection" tone as bridge line draws
- Each text line: subtle type-on or fade sound
- "Same math." landing: slightly deeper, more authoritative tone
- Ambient: subtle electronic hum suggesting precision/mathematics

## Visual Style Notes

- Teal (#2AA198) is critical -- it signals "chip design" from Part 2 and creates instant visual recognition
- This is a SIDEBAR, not main flow -- the framing should feel slightly set apart (accent lines, or a subtle background shift)
- The Synopsys icon must be recognizable as the same element from Part 2 Section 2.10 (the checkmark that morphed into the test suite)
- Z3 should feel like it belongs in the same visual family
- "Same math." is the punchline -- it gets the largest, boldest treatment
- 3Blue1Brown frequently uses these sidebar moments to drop a surprising connection; the tone should be "wait, really?" followed by "yes, literally the same"

## Transition

Continues directly into Section 3.9b (formal verification comparison) which expands this into a detailed side-by-side comparison.
