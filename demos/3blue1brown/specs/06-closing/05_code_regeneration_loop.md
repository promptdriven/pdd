# Section 6.5: Code Dissolves and Regenerates in a Loop

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 21:05 - 21:15

## Visual Description

The code in the center of the triangle dissolves and regenerates. Dissolves and regenerates. Each time slightly different but always passing all tests, always satisfying the prompt. A subtle terminal loop is visible: `pdd generate` -> code appears -> `pdd test` -> checkmark -> repeat. This is the key visual proof of disposability: the code is infinitely replaceable because the mold (prompts + tests + grounding) is what actually matters.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Triangle from Section 6.4 persists as context (dimmed slightly)

### Animation Elements

1. **Persistent Triangle (Background)**
   - Same triangle from 6.4, steady glow at reduced intensity (60%)
   - Vertices: PROMPT (blue), TESTS (amber), GROUNDING (green)
   - Edges visible but not animated
   - Provides context: the mold remains constant

2. **Center Code Block (Cycles)**
   - Positioned at triangle centroid
   - Shows abstract code lines (gray bars of varying width)
   - Each regeneration cycle produces slightly different bar patterns
   - Color: Neutral gray (#A0A0A0), no glow

3. **Dissolution Effect**
   - Code block fragments into particles
   - Particles scatter outward briefly
   - Color: Gray -> transparent
   - Duration per dissolution: ~1 second

4. **Regeneration Effect**
   - New particles coalesce from edges/vertices of triangle
   - Form a NEW code block (different line pattern)
   - Color: Transparent -> gray
   - Duration per regeneration: ~1 second

5. **Subtle Terminal Loop (Bottom)**
   - Small, understated terminal readout at bottom of frame
   - Shows cycling commands, not the focus of attention
   - `pdd generate` -> `parser.py` -> `pdd test` -> `✓` -> repeat

6. **Cycle Counter (Optional)**
   - Tiny counter: "v1", "v2", "v3"...
   - Appears briefly with each regeneration
   - Emphasizes that each version is different

### Visual Design

```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│                      PROMPT (dim glow)                       │
│                       /        \                             │
│                      /          \                            │
│                     /            \                           │
│                    /  ┌────────┐  \                          │
│                   /   │ ░░░░░░ │   \     <- dissolves        │
│                  /    │ ░░░░   │    \       and reforms      │
│                 /     │ ░░░░░  │     \      each cycle       │
│                /      └────────┘      \                      │
│               /         v2             \                     │
│           TESTS ─────────────────── GROUNDING               │
│           (dim glow)                (dim glow)               │
│                                                              │
│     ┌─ terminal ──────────────────────────────────────┐      │
│     │ $ pdd generate parser → pdd test → ✓  [loop]   │      │
│     └─────────────────────────────────────────────────┘      │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### Animation Sequence

The animation runs 2.5 cycles in 10 seconds (each cycle ~4 seconds, final cycle holds).

**Cycle 1 (Frame 0-120, 0-4s):**

1. **Frame 0-30 (0-1s):** Code v1 visible
   - Code block present in center (line pattern A)
   - Terminal shows: `✓ parser.py (v1)`
   - Brief hold

2. **Frame 30-60 (1-2s):** Dissolution
   - Code block fragments into particles
   - ~100 particles scatter outward
   - Particles fade as they travel
   - Terminal: `pdd generate parser...`

3. **Frame 60-90 (2-3s):** Regeneration
   - New particles flow from triangle edges toward center
   - Coalesce into new code block (line pattern B -- different widths)
   - Terminal: `Generated parser.py`

4. **Frame 90-120 (3-4s):** Verify
   - Code v2 stable in center
   - Green flash/checkmark at code block
   - Terminal: `pdd test → ✓`

**Cycle 2 (Frame 120-240, 4-8s):**

5. **Frame 120-150 (4-5s):** Code v2 holds briefly
6. **Frame 150-180 (5-6s):** Dissolution (same as step 2, different particle paths)
7. **Frame 180-210 (6-7s):** Regeneration into v3 (line pattern C)
8. **Frame 210-240 (7-8s):** Verify with checkmark

**Final Hold (Frame 240-300, 8-10s):**

9. **Frame 240-300 (8-10s):** v3 stable, triangle glows
   - Hold the complete picture
   - Triangle steady, code present but unremarkable
   - Terminal shows final `✓`
   - Message clear: this can repeat forever

### Code Structure (Remotion)

```typescript
const CodeRegenerationLoop: React.FC = () => {
  const frame = useCurrentFrame();
  const cycleLength = 120; // 4 seconds per cycle at 30fps

  // Current cycle index
  const cycleIndex = Math.floor(frame / cycleLength);
  const cycleFrame = frame % cycleLength;

  // Triangle background (persistent, dimmed)
  const triangleOpacity = 0.6;

  // Code block state within cycle
  const isDissolving = cycleFrame >= 30 && cycleFrame < 60;
  const isRegenerating = cycleFrame >= 60 && cycleFrame < 90;
  const isVerifying = cycleFrame >= 90;
  const isHolding = cycleFrame < 30;

  // Dissolution progress
  const dissolveProgress = interpolate(
    cycleFrame,
    [30, 60],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Regeneration progress
  const regenProgress = interpolate(
    cycleFrame,
    [60, 90],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Verification checkmark
  const checkOpacity = interpolate(
    cycleFrame,
    [90, 100, 115, 120],
    [0, 1, 1, 0.5],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Hold on final cycle
  const isFinalHold = frame >= 240;

  // Generate different code line patterns per cycle
  const codePattern = useMemo(() => {
    return generateCodePattern(cycleIndex);
  }, [cycleIndex]);

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Persistent triangle (dimmed) */}
      <TriangleDiagram opacity={triangleOpacity} showSubLabels={false} />

      {/* Code block lifecycle */}
      {(isHolding || isFinalHold) && (
        <CodeBlock
          pattern={codePattern}
          opacity={0.5}
          label={`v${cycleIndex + 1}`}
        />
      )}

      {isDissolving && !isFinalHold && (
        <DissolutionEffect
          progress={dissolveProgress}
          particleCount={100}
          sourcePattern={codePattern}
        />
      )}

      {isRegenerating && !isFinalHold && (
        <RegenerationEffect
          progress={regenProgress}
          particleCount={100}
          targetPattern={generateCodePattern(cycleIndex + 1)}
          triangleVertices={vertices}
        />
      )}

      {/* Verification checkmark */}
      {isVerifying && (
        <div style={{
          position: 'absolute',
          left: 960,
          top: 520,
          transform: 'translate(-50%, -50%)',
          color: '#5AAA6E',
          fontSize: 24,
          opacity: checkOpacity,
        }}>
          ✓
        </div>
      )}

      {/* Subtle terminal readout */}
      <TerminalLoop
        frame={frame}
        cycleLength={cycleLength}
      />
    </AbsoluteFill>
  );
};
```

### Code Pattern Generator

```typescript
const generateCodePattern = (seed: number): number[] => {
  // Generate different-looking code line widths for each cycle
  const rng = seedRandom(seed);
  const lineCount = 5 + Math.floor(rng() * 3);
  return Array.from({ length: lineCount }, () =>
    30 + Math.floor(rng() * 60) // Width percentages
  );
};

const CodeBlock: React.FC<{
  pattern: number[];
  opacity: number;
  label: string;
}> = ({ pattern, opacity, label }) => {
  return (
    <div style={{
      position: 'absolute',
      left: 900,
      top: 410,
      width: 120,
      opacity,
    }}>
      <div style={{
        backgroundColor: 'rgba(160, 160, 160, 0.1)',
        border: '1px solid rgba(160, 160, 160, 0.2)',
        borderRadius: 6,
        padding: 10,
      }}>
        {pattern.map((width, i) => (
          <div key={i} style={{
            height: 4,
            backgroundColor: 'rgba(160, 160, 160, 0.35)',
            marginBottom: 3,
            borderRadius: 2,
            width: `${width}%`,
          }} />
        ))}
      </div>
      <div style={{
        textAlign: 'center',
        fontSize: 11,
        color: 'rgba(160, 160, 160, 0.4)',
        marginTop: 4,
      }}>
        {label}
      </div>
    </div>
  );
};
```

### Terminal Loop Component

```typescript
const TerminalLoop: React.FC<{
  frame: number;
  cycleLength: number;
}> = ({ frame, cycleLength }) => {
  const cycleFrame = frame % cycleLength;

  let terminalText = '';
  let textColor = 'rgba(255, 255, 255, 0.4)';

  if (cycleFrame < 30) {
    terminalText = '✓ All tests passed';
    textColor = 'rgba(90, 170, 110, 0.6)';
  } else if (cycleFrame < 60) {
    terminalText = '$ pdd generate parser...';
    textColor = 'rgba(74, 144, 217, 0.6)';
  } else if (cycleFrame < 90) {
    terminalText = 'Regenerating parser.py...';
    textColor = 'rgba(255, 255, 255, 0.4)';
  } else {
    terminalText = '$ pdd test parser → ✓';
    textColor = 'rgba(90, 170, 110, 0.6)';
  }

  return (
    <div style={{
      position: 'absolute',
      bottom: 60,
      left: '50%',
      transform: 'translateX(-50%)',
      backgroundColor: 'rgba(30, 30, 46, 0.7)',
      borderRadius: 8,
      padding: '8px 20px',
      fontFamily: 'JetBrains Mono, monospace',
      fontSize: 13,
      color: textColor,
      border: '1px solid rgba(255, 255, 255, 0.08)',
    }}>
      {terminalText}
    </div>
  );
};
```

### Particle System

```typescript
const DissolutionEffect: React.FC<{
  progress: number;
  particleCount: number;
  sourcePattern: number[];
}> = ({ progress, particleCount }) => {
  const particles = useMemo(() =>
    Array.from({ length: particleCount }, (_, i) => ({
      id: i,
      angle: (i / particleCount) * Math.PI * 2 + Math.random() * 0.8,
      distance: 40 + Math.random() * 80,
      delay: Math.random() * 0.3,
      size: 2 + Math.random() * 3,
    })), [particleCount]);

  return (
    <>
      {particles.map(p => {
        const t = Math.max(0, Math.min(1, (progress - p.delay) / (1 - p.delay)));
        const eased = Easing.out(Easing.quad)(t);
        return (
          <div key={p.id} style={{
            position: 'absolute',
            left: 960 + Math.cos(p.angle) * eased * p.distance,
            top: 480 + Math.sin(p.angle) * eased * p.distance,
            width: p.size,
            height: p.size,
            borderRadius: '50%',
            backgroundColor: `rgba(160, 160, 160, ${0.5 * (1 - eased)})`,
          }} />
        );
      })}
    </>
  );
};
```

### Easing

- Dissolution particles: `easeOutQuad` (fast scatter, slow fade)
- Regeneration particles: `easeInCubic` (accelerate toward center)
- Checkmark appearance: `easeOutBack` (pop)
- Triangle background: Constant (no easing, just persistent)

## Narration Sync

> "Code is generated, verified, and disposable."

"Generated" lands as the first regeneration completes. "Verified" hits on the checkmark. "Disposable" lands as the second dissolution begins -- the audience sees the code literally dissolve as the word is spoken.

## Audio Notes

- Dissolution: Soft "scatter" or digital dissolve sound (brief, clean)
- Regeneration: Reverse scatter, coalescing tone
- Checkmark: Quiet bright chime
- Harmonious resolution when code regenerates clean (per script sound design notes)
- The loop should create a rhythmic, almost musical pattern
- Each cycle slightly different in timing to avoid mechanical feel

## Visual Style Notes

- The key message is: THE CODE CHANGES, THE MOLD DOES NOT
- The triangle remains rock-solid while the center churns
- Each code version should be visibly different (different bar widths/counts)
- But the triangle never wavers -- stability vs. disposability
- The particle effects should feel effortless, not dramatic
- This is a callback to Section 2.9 (plastic regenerates) now in code form
- The terminal readout is SUBTLE -- background information, not the focus
- 3Blue1Brown aesthetic: clean particle systems, mathematical feel

## Transition

The loop settles into the final hold, which transitions to Section 6.6 -- the final frame where the mold glows and the code is unremarkable.
