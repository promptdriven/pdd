# Section 3.17: Three Components Working Together

**Tool:** Remotion
**Duration:** ~25 seconds
**Timestamp:** 13:00 - 13:25

## Visual Description

Pull back to see all three components working together. Prompt flows in → passes through grounding → fills the mold → constrained by test walls → code emerges. The complete PDD system visualized as an integrated whole.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Full system view

### Animation Elements

1. **Complete Mold System**
   - Cross-section with all three labeled parts
   - Nozzle (blue, prompt)
   - Walls (amber, tests)
   - Interior (green, grounding)

2. **Flow Animation**
   - Prompt text enters nozzle
   - Transforms through grounding
   - Fills space constrained by walls
   - Code emerges at output

3. **Component Labels**
   - "PROMPT" → "Intent"
   - "TESTS" → "Constraints"
   - "GROUNDING" → "Style"

4. **Integration Formula**
   - "Prompt + Tests + Grounding"
   - "Intent + Constraints + Style"
   - "= Complete Specification"

### Animation Sequence

1. **Frame 0-120 (0-4s):** System overview
   - Full mold system fades in
   - All three components visible
   - Ready for demonstration

2. **Frame 120-240 (4-8s):** Prompt enters
   - Blue glow at nozzle
   - Prompt text flows in
   - "Intent" label appears

3. **Frame 240-360 (8-12s):** Through grounding
   - Green glow in interior
   - Material transforms (style applied)
   - "Style" label appears

4. **Frame 360-480 (12-16s):** Constrained by walls
   - Amber walls glow
   - Material hits boundaries
   - "Constraints" label appears

5. **Frame 480-600 (16-20s):** Code emerges
   - Output appears at bottom
   - Clean, styled, tested code
   - Success indicator

6. **Frame 600-750 (20-25s):** Integration formula
   - Formula appears: "Prompt + Tests + Grounding"
   - Translates: "Intent + Constraints + Style"
   - Equals: "Complete Specification"

### Visual Design: Integrated System

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│                    ┌───────────────┐                        │
│        Intent ─────│    PROMPT     │───── Blue (#4A90D9)    │
│                    │    (Nozzle)   │                        │
│                    └───────┬───────┘                        │
│                            │                                │
│                            ▼                                │
│                    ┌───────────────┐                        │
│         Style ─────│   GROUNDING   │───── Green (#5AAA6E)   │
│                    │  (Material)   │                        │
│                    └───────┬───────┘                        │
│                            │                                │
│               ┌────────────┼────────────┐                   │
│               │            │            │                   │
│   Constraints │   █████████▼█████████   │ Amber (#D9944A)   │
│               │   █                 █   │                   │
│               │   █   [Code fills]  █   │ ← TESTS (Walls)   │
│               │   █                 █   │                   │
│               │   █████████████████████   │                   │
│               └─────────────────────────┘                   │
│                            │                                │
│                            ▼                                │
│                    ┌───────────────┐                        │
│                    │ Generated Code │                        │
│                    │     ✓ ✓ ✓      │                        │
│                    └───────────────┘                        │
│                                                             │
│  ═══════════════════════════════════════════════════════   │
│  │ Prompt + Tests + Grounding = Complete Specification │   │
│  │ Intent + Constraints + Style                        │   │
│  ═══════════════════════════════════════════════════════   │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

### Code Structure (Remotion)

```typescript
const ThreeComponents: React.FC = () => {
  const frame = useCurrentFrame();

  // System visibility
  const systemOpacity = interpolate(
    frame,
    [0, 90],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Prompt flow
  const promptGlow = interpolate(
    frame,
    [120, 180, 240],
    [0, 1, 0.3],
    { extrapolateRight: 'clamp' }
  );

  // Grounding processing
  const groundingGlow = interpolate(
    frame,
    [240, 300, 360],
    [0, 1, 0.3],
    { extrapolateRight: 'clamp' }
  );

  // Wall constraint
  const wallGlow = interpolate(
    frame,
    [360, 420, 480],
    [0, 1, 0.4],
    { extrapolateRight: 'clamp' }
  );

  // Code output
  const codeOpacity = interpolate(
    frame,
    [480, 540],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Formula
  const formulaOpacity = interpolate(
    frame,
    [600, 660],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Full system diagram */}
      <div style={{ opacity: systemOpacity }}>
        {/* Prompt/Nozzle */}
        <ComponentBlock
          type="prompt"
          label="PROMPT"
          sublabel="Intent"
          color="#4A90D9"
          glowIntensity={promptGlow}
          position={{ x: 960, y: 120 }}
        />

        {/* Flow arrow 1 */}
        <FlowArrow from="prompt" to="grounding" active={frame > 120} />

        {/* Grounding */}
        <ComponentBlock
          type="grounding"
          label="GROUNDING"
          sublabel="Style"
          color="#5AAA6E"
          glowIntensity={groundingGlow}
          position={{ x: 960, y: 300 }}
        />

        {/* Flow arrow 2 */}
        <FlowArrow from="grounding" to="walls" active={frame > 240} />

        {/* Test Walls */}
        <WallsBlock
          label="TESTS"
          sublabel="Constraints"
          color="#D9944A"
          glowIntensity={wallGlow}
          position={{ x: 960, y: 480 }}
        />

        {/* Flow arrow 3 */}
        <FlowArrow from="walls" to="output" active={frame > 360} />

        {/* Code Output */}
        <OutputBlock
          opacity={codeOpacity}
          position={{ x: 960, y: 680 }}
        />
      </div>

      {/* Integration formula */}
      <IntegrationFormula opacity={formulaOpacity} />
    </AbsoluteFill>
  );
};
```

### Component Block

```typescript
const ComponentBlock: React.FC<{
  type: string;
  label: string;
  sublabel: string;
  color: string;
  glowIntensity: number;
  position: Point;
}> = ({ type, label, sublabel, color, glowIntensity, position }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      transform: 'translateX(-50%)',
      textAlign: 'center',
    }}>
      <div style={{
        width: 180,
        height: 70,
        background: `rgba(${hexToRgb(color)}, 0.15)`,
        border: `2px solid ${color}`,
        borderRadius: 12,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        boxShadow: `0 0 ${30 * glowIntensity}px ${color}`,
      }}>
        <span style={{
          fontSize: 18,
          fontWeight: 'bold',
          color: color,
        }}>
          {label}
        </span>
      </div>
      <div style={{
        marginTop: 8,
        fontSize: 14,
        color: '#888',
      }}>
        {sublabel}
      </div>
    </div>
  );
};
```

### Integration Formula

```typescript
const IntegrationFormula: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <div style={{
      position: 'absolute',
      bottom: 60,
      left: '50%',
      transform: 'translateX(-50%)',
      opacity,
      textAlign: 'center',
    }}>
      <div style={{
        fontSize: 24,
        color: '#FFF',
        fontWeight: 'bold',
        marginBottom: 8,
      }}>
        <span style={{ color: '#4A90D9' }}>Prompt</span>
        {' + '}
        <span style={{ color: '#D9944A' }}>Tests</span>
        {' + '}
        <span style={{ color: '#5AAA6E' }}>Grounding</span>
      </div>
      <div style={{
        fontSize: 18,
        color: '#888',
      }}>
        Intent + Constraints + Style
      </div>
      <div style={{
        fontSize: 20,
        color: '#FFF',
        marginTop: 8,
      }}>
        = Complete Specification
      </div>
    </div>
  );
};
```

### Easing

- System fade: `easeOutCubic`
- Component glows: `easeOutQuad`
- Flow arrows: `easeOutQuad`
- Code output: `easeOutCubic`
- Formula: `easeOutCubic`

## Narration Sync

> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."

Each component glows as its name is spoken. The formula appears during "complete specification".

## Audio Notes

- Three distinct tones for three components
- Building harmony as they combine
- Resolution chord on "complete specification"
- Satisfying integration feeling

## Visual Style Notes

- All three colors visible simultaneously
- Flow shows the process clearly
- Labels make concepts explicit
- Formula is the key takeaway
- 3Blue1Brown: mathematical elegance

## Transition

Continues into Section 3.18 - the final beat where code fades and mold glows.
