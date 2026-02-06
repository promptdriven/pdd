# Section 3.4: Focus on Single Wall

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 11:20 - 11:30

## Visual Description

Camera zooms in on a single wall segment labeled "null → None". The liquid (code generation) approaches, hits the wall, and stops completely. This tight focus emphasizes that the model CANNOT generate code that violates this constraint.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Zoomed view (2-3x magnification)

### Animation Elements

1. **Wall Close-Up**
   - Single wall segment dominates frame
   - "null → None" label clearly visible
   - Wall has texture detail visible at zoom

2. **Approaching Liquid**
   - Code-like liquid flows toward wall
   - Slight code snippets visible in liquid (optional)
   - Momentum visible in flow

3. **Impact Moment**
   - Liquid hits wall
   - Brief splash/compression effect
   - Wall flashes brighter
   - Liquid stops DEAD

4. **Held State**
   - Liquid pressed against wall
   - Cannot pass through
   - Visual tension at the boundary

### Animation Sequence

1. **Frame 0-90 (0-3s):** Zoom in
   - Camera pushes in on "null → None" wall
   - Other walls blur/fade
   - Focus narrows

2. **Frame 90-150 (3-5s):** Liquid approaches
   - Fluid flows toward wall from right
   - Building momentum
   - Wall awaits

3. **Frame 150-180 (5-6s):** Impact
   - Liquid contacts wall
   - Brief compression effect
   - Wall glows bright amber
   - Liquid STOPS

4. **Frame 180-300 (6-10s):** Hold on constraint
   - Liquid pressed against wall
   - Wall firm and immutable
   - The constraint is absolute
   - Hold for narration impact

### Visual Design: Close-Up View

```
┌────────────────────────────────────┐
│                                    │
│         ┌──────────────┐           │
│         │              │           │
│    ▓▓▓▓▓│  null → None │           │
│    ▓▓▓▓▓│              │           │
│    ▓▓▓▓▓│  ████████████│           │
│    ▓▓▓▓▓│              │           │
│    ▓▓▓▓▓│              │           │
│         └──────────────┘           │
│                                    │
└────────────────────────────────────┘
  ^liquid    ^wall (amber glow)
```

### Code Structure (Remotion)

```typescript
const FocusSingleWall: React.FC = () => {
  const frame = useCurrentFrame();

  // Zoom progress
  const zoom = interpolate(
    frame,
    [0, 90],
    [1, 2.5],
    { extrapolateRight: 'clamp' }
  );

  // Liquid position (approaching wall at x=0)
  const liquidX = interpolate(
    frame,
    [90, 150],
    [200, 0], // Approaches from right, stops at wall
    { extrapolateRight: 'clamp' }
  );

  // Impact glow
  const impactGlow = interpolate(
    frame,
    [150, 160, 180],
    [0, 1, 0.4],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <div style={{ transform: `scale(${zoom})` }}>
        <WallSegment
          label="null → None"
          glowIntensity={impactGlow}
        />
        <LiquidMass
          x={liquidX}
          compressed={frame > 150}
        />
      </div>
    </AbsoluteFill>
  );
};
```

### Impact Effect Details

```typescript
const ImpactEffect: React.FC<{ frame: number }> = ({ frame }) => {
  const IMPACT_FRAME = 150;

  if (frame < IMPACT_FRAME) return null;

  const elapsed = frame - IMPACT_FRAME;

  // Ripple effect on wall
  const rippleRadius = interpolate(elapsed, [0, 30], [0, 50]);
  const rippleOpacity = interpolate(elapsed, [0, 30], [0.8, 0]);

  // Liquid compression
  const compression = interpolate(elapsed, [0, 10, 30], [0, 0.1, 0]);

  return (
    <>
      <RippleRing radius={rippleRadius} opacity={rippleOpacity} />
      <CompressionWave intensity={compression} />
    </>
  );
};
```

### Easing

- Zoom: `easeOutCubic`
- Liquid approach: `easeInQuad` (building momentum)
- Impact stop: Instant (no easing - hard stop)
- Wall glow: `easeOutQuad`

## Narration Sync

> "When the model generates code, it sees these tests. The code it produces must pass them. It literally cannot generate code that violates these walls."

The word "literally" lands as the liquid stops dead at the wall.

## Audio Notes

- Soft "whoosh" of approaching liquid
- Sharp "thud" on impact
- Brief silence after impact (emphasis)
- Subtle hum of constraint holding

## Visual Style Notes

- This is THE moment of constraint visualization
- The stop must be absolute, not gradual
- Wall is immovable, unchangeable
- The model has no choice - this is physics

## Transition

Cut to Section 3.5 where a bug is discovered, setting up the "add a wall" concept.
