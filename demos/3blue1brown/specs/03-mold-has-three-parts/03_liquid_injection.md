# Section 3.3: Liquid Injection

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 9:15 - 9:30

## Visual Description

Liquid (representing code generation) flows into the mold cavity from the nozzle. The liquid flows freely until it encounters a wall, then stops abruptly. The shape is constrained by the test walls—a visceral demonstration of how tests limit generated code.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continuation from Section 3.2

### Animation Elements

1. **Liquid Flow**
   - Starts from blue nozzle at top
   - Color: Gray with blue tint (#8A9CAF) - represents code
   - Fluid physics simulation (simplified)
   - Viscous movement, not water-like

2. **Wall Interaction**
   - Liquid hits walls and STOPS
   - Brief splash/impact effect
   - Wall glows brighter momentarily on contact
   - No liquid passes through

3. **Cavity Fill**
   - Liquid spreads to fill available space
   - Takes the exact shape defined by walls
   - Smooth, satisfying fill animation

### Animation Sequence

1. **Frame 0-60 (0-2s):** Preparation
   - Mold with labeled walls visible
   - Nozzle pulses blue
   - Anticipation builds

2. **Frame 60-120 (2-4s):** Injection begins
   - Liquid emerges from nozzle
   - Flows downward
   - Smooth, controlled stream

3. **Frame 120-180 (4-6s):** First wall contact
   - Liquid reaches top wall
   - Impact effect - brief glow
   - Liquid spreads horizontally
   - Wall holds firm

4. **Frame 180-270 (6-9s):** Spreading and constraining
   - Liquid flows along walls
   - Each wall contact triggers brief highlight
   - Shape emerges from constraints

5. **Frame 270-360 (9-12s):** Cavity fills
   - All space within walls fills
   - Liquid settles into final shape
   - Perfect conformity to mold

6. **Frame 360-450 (12-15s):** Hold on result
   - Filled cavity visible
   - Walls still glowing amber
   - The constrained shape is the output

### Physics Simulation

```typescript
// Simplified fluid behavior
interface FluidParticle {
  x: number;
  y: number;
  vx: number;
  vy: number;
}

const simulateFluid = (particles: FluidParticle[], walls: Wall[]) => {
  particles.forEach(p => {
    // Gravity
    p.vy += 0.1;

    // Move
    p.x += p.vx;
    p.y += p.vy;

    // Wall collision
    walls.forEach(wall => {
      if (collides(p, wall)) {
        // Stop at wall
        reflectAndDampen(p, wall);
      }
    });
  });
};
```

### Visual Design: Flow Stages

```
Stage 1: Injection       Stage 2: Contact        Stage 3: Fill
    ↓                        ↓                       ↓
   ███                      ███                     ███
    │                      ▓▓▓▓▓                   ▓▓▓▓▓
    ▓                     ▓     ▓                 ▓▓▓▓▓▓▓
    ▓                    ▓       ▓               ▓▓▓▓▓▓▓▓▓
                        ▓         ▓             ▓▓▓▓▓▓▓▓▓▓▓
   ███                   ███████████              ███████████
```

### Code Structure (Remotion)

```typescript
const LiquidInjection: React.FC = () => {
  const frame = useCurrentFrame();

  // Flow progress: 0 = start, 1 = fully filled
  const flowProgress = interpolate(
    frame,
    [60, 300],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Wall glow intensity on contact
  const wallGlow = (wallIndex: number, contactFrame: number) => {
    return interpolate(
      frame,
      [contactFrame, contactFrame + 15, contactFrame + 45],
      [0, 1, 0.3],
      { extrapolateRight: 'clamp' }
    );
  };

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <MoldCrossSection />
      <WallsWithLabels />
      <FluidSimulation progress={flowProgress} />
      <WallImpactEffects frame={frame} />
      <Nozzle glowing={frame < 120} />
    </AbsoluteFill>
  );
};
```

### Color Palette

- Liquid/Code: Gray-blue (#8A9CAF)
- Wall glow on impact: Brighter amber (#FFAA55)
- Nozzle: Blue (#4A90D9)
- Background cavity: Darker (#0D0D1A)

### Easing

- Liquid flow: Physics-based (gravity + damping)
- Wall impact glow: `easeOutQuad`
- Fill settling: `easeOutExpo`

## Narration Sync

> "Each test is a constraint. A boundary the generated code cannot cross."

The liquid visibly stops at each wall as "constraint" and "boundary" are spoken.

## Audio Notes

- Soft "whoosh" as liquid flows
- Subtle "thud" on wall contact
- Satisfying "settle" sound as cavity fills
- Walls might hum slightly when contacted

## Visual Style Notes

- The constraint is visceral and physical
- Walls are immovable, unyielding
- Liquid MUST conform - there's no other option
- This is the core visual metaphor of test-driven constraint

## Transition

Continues into Section 3.4 with a close-up on a single wall interaction.
