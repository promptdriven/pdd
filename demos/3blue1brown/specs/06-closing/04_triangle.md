# Section 6.4: The Triangle -- Prompt, Tests, Grounding

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 20:55 - 21:05

## Visual Description

The three components appear as a triangle: PROMPT at the top, TESTS at the bottom left, GROUNDING at the bottom right. Each vertex uses its signature color and glows steadily. Code appears in the center of the triangle, generated from the three -- present but gray and unglowing. This is the crystallization of the entire framework into a single, elegant diagram.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Triangle centered in frame

### Animation Elements

1. **Triangle Vertices**
   - Three nodes at equilateral triangle positions
   - Each node: rounded rectangle with label and glow
   - PROMPT (top center): Blue (#4A90D9)
   - TESTS (bottom left): Amber (#D9944A)
   - GROUNDING (bottom right): Green (#5AAA6E)

2. **Triangle Edges**
   - Lines connecting the three vertices
   - Color: Gradient between the two connected vertex colors
   - Subtle animated pulse along edges (energy flowing)
   - Line width: 2px with glow

3. **Center Code Block**
   - Positioned at the centroid of the triangle
   - Label: "Generated Code"
   - Color: Neutral gray (#A0A0A0) at 50% opacity
   - NO glow -- critically important
   - Smaller than the vertex nodes

4. **Derivation Arrows**
   - Three arrows from edges/vertices pointing inward toward center code
   - Dashed, subtle
   - Indicate that code is derived FROM the three components

5. **Vertex Sub-labels**
   - Below each vertex label, smaller text:
   - PROMPT: "encodes intent"
   - TESTS: "preserves behavior"
   - GROUNDING: "maintains style"

### Visual Design

```
┌──────────────────────────────────────────────────────────────┐
│                                                              │
│                        PROMPT                                │
│                     ✦ encodes intent ✦                       │
│                      (#4A90D9, glow)                         │
│                       /        \                             │
│                      /          \                            │
│                     /            \                           │
│                    /   Generated  \                          │
│                   /     Code       \                         │
│                  /    (gray, dim)   \                        │
│                 /                    \                       │
│                /                      \                      │
│           TESTS ────────────────── GROUNDING                 │
│      ✦ preserves behavior ✦    ✦ maintains style ✦          │
│        (#D9944A, glow)          (#5AAA6E, glow)              │
│                                                              │
└──────────────────────────────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Vertices appear
   - PROMPT vertex fades in first (top, blue)
   - TESTS vertex follows 10 frames later (bottom-left, amber)
   - GROUNDING vertex follows 10 frames later (bottom-right, green)
   - Each appears with a scale-up animation (0 -> 1)

2. **Frame 60-120 (2-4s):** Edges connect
   - Lines draw between vertices, connecting the triangle
   - Each line draws in ~20 frames
   - Gradient colors along each edge
   - Subtle pulse animation begins along edges

3. **Frame 120-180 (4-6s):** Glows intensify + sub-labels
   - All three vertices pulse brighter simultaneously
   - Sub-labels fade in: "encodes intent", "preserves behavior", "maintains style"
   - The triangle is now complete and glowing

4. **Frame 180-240 (6-8s):** Code appears in center
   - Gray code block fades in at centroid
   - "Generated Code" label appears
   - Derivation arrows (dashed) point inward from edges
   - Code is deliberately understated -- no glow, lower opacity

5. **Frame 240-300 (8-10s):** Hold complete diagram
   - Triangle stable with steady glows
   - Code present but receding
   - The visual hierarchy is clear: glowing triangle matters, gray center does not
   - Hold for narration to land

### Code Structure (Remotion)

```typescript
const TriangleDiagram: React.FC = () => {
  const frame = useCurrentFrame();

  // Triangle geometry (centered on canvas)
  const centerX = 960;
  const centerY = 480;
  const radius = 280;

  const vertices = {
    prompt:    { x: centerX, y: centerY - radius, color: '#4A90D9', label: 'PROMPT', sub: 'encodes intent' },
    tests:     { x: centerX - radius * 0.866, y: centerY + radius * 0.5, color: '#D9944A', label: 'TESTS', sub: 'preserves behavior' },
    grounding: { x: centerX + radius * 0.866, y: centerY + radius * 0.5, color: '#5AAA6E', label: 'GROUNDING', sub: 'maintains style' },
  };

  // Vertex appearance (staggered)
  const vertexScale = (delay: number) => interpolate(
    frame,
    [delay, delay + 30],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.back(1.5)) }
  );

  // Edge draw progress
  const edgeProgress = interpolate(
    frame,
    [60, 120],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Glow intensification
  const glowPulse = interpolate(
    frame,
    [120, 160],
    [0.6, 1.0],
    { extrapolateRight: 'clamp' }
  );

  // Sub-label opacity
  const subLabelOpacity = interpolate(
    frame,
    [130, 170],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Center code appearance
  const codeOpacity = interpolate(
    frame,
    [180, 220],
    [0, 0.5],
    { extrapolateRight: 'clamp' }
  );

  // Derivation arrows
  const arrowOpacity = interpolate(
    frame,
    [200, 240],
    [0, 0.3],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Triangle edges (SVG) */}
      <svg style={{ position: 'absolute', width: '100%', height: '100%' }}>
        <TriangleEdge
          from={vertices.prompt}
          to={vertices.tests}
          progress={edgeProgress}
          glowIntensity={glowPulse}
        />
        <TriangleEdge
          from={vertices.tests}
          to={vertices.grounding}
          progress={edgeProgress}
          glowIntensity={glowPulse}
        />
        <TriangleEdge
          from={vertices.grounding}
          to={vertices.prompt}
          progress={edgeProgress}
          glowIntensity={glowPulse}
        />

        {/* Derivation arrows to center */}
        <DerivationArrows
          vertices={vertices}
          center={{ x: centerX, y: centerY }}
          opacity={arrowOpacity}
        />
      </svg>

      {/* Vertex nodes */}
      {Object.entries(vertices).map(([key, v], i) => (
        <VertexNode
          key={key}
          label={v.label}
          subLabel={v.sub}
          color={v.color}
          position={v}
          scale={vertexScale(i * 10)}
          glowIntensity={glowPulse}
          subLabelOpacity={subLabelOpacity}
        />
      ))}

      {/* Center code block (NO GLOW) */}
      <div style={{
        position: 'absolute',
        left: centerX - 80,
        top: centerY - 30,
        width: 160,
        textAlign: 'center',
        opacity: codeOpacity,
      }}>
        <div style={{
          backgroundColor: 'rgba(160, 160, 160, 0.1)',
          border: '1px solid rgba(160, 160, 160, 0.25)',
          borderRadius: 8,
          padding: '12px 16px',
          fontFamily: 'monospace',
          fontSize: 13,
          color: 'rgba(160, 160, 160, 0.6)',
        }}>
          Generated Code
        </div>
      </div>
    </AbsoluteFill>
  );
};
```

### Vertex Node Component

```typescript
const VertexNode: React.FC<{
  label: string;
  subLabel: string;
  color: string;
  position: { x: number; y: number };
  scale: number;
  glowIntensity: number;
  subLabelOpacity: number;
}> = ({ label, subLabel, color, position, scale, glowIntensity, subLabelOpacity }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      transform: `translate(-50%, -50%) scale(${scale})`,
      textAlign: 'center',
    }}>
      <div style={{
        backgroundColor: `rgba(${hexToRgb(color)}, 0.15)`,
        border: `2px solid ${color}`,
        borderRadius: 12,
        padding: '14px 24px',
        boxShadow: `0 0 ${30 * glowIntensity}px ${color}`,
        minWidth: 140,
      }}>
        <span style={{
          fontSize: 20,
          fontWeight: 'bold',
          color: color,
          letterSpacing: 2,
        }}>
          {label}
        </span>
      </div>
      <div style={{
        marginTop: 10,
        fontSize: 15,
        color: 'rgba(255, 255, 255, 0.6)',
        fontStyle: 'italic',
        opacity: subLabelOpacity,
      }}>
        {subLabel}
      </div>
    </div>
  );
};
```

### Triangle Edge Component

```typescript
const TriangleEdge: React.FC<{
  from: { x: number; y: number; color: string };
  to: { x: number; y: number; color: string };
  progress: number;
  glowIntensity: number;
}> = ({ from, to, progress, glowIntensity }) => {
  const dx = to.x - from.x;
  const dy = to.y - from.y;

  return (
    <>
      {/* Glow layer */}
      <line
        x1={from.x}
        y1={from.y}
        x2={from.x + dx * progress}
        y2={from.y + dy * progress}
        stroke={from.color}
        strokeWidth={6}
        opacity={0.2 * glowIntensity}
        filter="blur(4px)"
      />
      {/* Main line with gradient */}
      <line
        x1={from.x}
        y1={from.y}
        x2={from.x + dx * progress}
        y2={from.y + dy * progress}
        stroke="url(#edgeGradient)"
        strokeWidth={2}
        opacity={0.8}
      />
    </>
  );
};
```

### Easing

- Vertex appearance: `easeOutBack` (slight overshoot for pop)
- Edge drawing: `easeOutCubic` (smooth draw)
- Glow intensification: `easeOutQuad`
- Sub-labels: `easeOutCubic`
- Code appearance: `easeOutQuad` (gentle, understated)

## Narration Sync

> "Prompts encode intent. Tests preserve behavior. Grounding maintains style."

Each clause lands as its corresponding vertex glows brighter:
- "Prompts encode intent" -> PROMPT vertex pulses
- "Tests preserve behavior" -> TESTS vertex pulses
- "Grounding maintains style" -> GROUNDING vertex pulses

The sub-labels appear in sync with the spoken words, reinforcing the mapping.

## Audio Notes

- Three ascending tones as vertices appear (low, mid, high)
- Harmonic chord as edges connect and triangle completes
- Subtle, sustained harmony during hold
- No tone for the center code block -- it is just output
- 3Blue1Brown style: mathematical, clean audio cues

## Visual Style Notes

- The triangle should feel like a definitive diagram -- the kind you remember
- Equilateral triangle for visual balance and mathematical elegance
- The glow-vs-no-glow contrast in the center is the visual thesis
- Colors should be vivid against the dark background
- Sub-labels in italic to differentiate from main labels
- This is the "one diagram that summarizes everything" moment
- 3Blue1Brown influence: clean lines, purposeful color, clear hierarchy

## Transition

The triangle holds as the view transitions to Section 6.5, where the center code block begins dissolving and regenerating in a loop.
