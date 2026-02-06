# Section 4.5: Animate Along the Curve

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 17:00 - 17:15

## Visual Description

A marker animates along the inverse curve, demonstrating the tradeoff. At the left (few tests), a large prompt icon appears with few amber walls. As the marker moves right (many tests), the prompt shrinks and amber walls multiply. This makes the tradeoff visceral.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Builds on graph from Section 4.4

### Animation Elements

1. **Moving Marker**
   - Glowing dot on the curve
   - Travels from left to right
   - Leaves subtle trail

2. **Prompt Size Indicator (LEFT)**
   - Large blue prompt icon when marker is left
   - Shrinks as marker moves right
   - Represents prompt complexity

3. **Test Wall Count (RIGHT)**
   - Few amber walls when marker is left
   - Walls multiply as marker moves right
   - Represents test accumulation

4. **Position Labels**
   - "FEW TESTS" at left position
   - "MANY TESTS" at right position
   - Subtle, contextual

### Visual Design

```
LEFT POSITION:                    RIGHT POSITION:
┌──────────────────────┐          ┌──────────────────────┐
│                      │          │                      │
│  ┌─────────────┐     │          │  ┌───┐               │
│  │             │     │          │  │   │  ║ ║ ║ ║ ║    │
│  │   PROMPT    │  ║  │          │  │PRO│  ║ ║ ║ ║ ║    │
│  │   (large)   │  ║  │   ──→    │  │MPT│  ║ ║ ║ ║ ║    │
│  │             │     │          │  │   │  ║ ║ ║ ║ ║    │
│  └─────────────┘     │          │  └───┘  ║ ║ ║ ║ ║    │
│                      │          │         (many walls) │
│     FEW TESTS        │          │     MANY TESTS       │
└──────────────────────┘          └──────────────────────┘
   ^marker here                      ^marker here
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Setup
   - Graph visible from 4.4
   - Marker appears at left of curve
   - Large prompt icon appears
   - 2-3 test walls visible

2. **Frame 60-300 (2-10s):** Marker travels
   - Marker moves along curve from left to right
   - Prompt icon smoothly shrinks
   - Test walls multiply (2 → 5 → 10 → 20+)
   - Continuous, satisfying animation

3. **Frame 300-390 (10-13s):** Arrive at right
   - Marker reaches right end of curve
   - Prompt icon now small
   - Many test walls visible
   - Hold briefly

4. **Frame 390-450 (13-15s):** Emphasis
   - Slight pulse on final state
   - Contrast between start and end is clear
   - Ready for transition

### Code Structure (Remotion)

```typescript
const AnimateCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Marker position along curve (0 to 1)
  const curveProgress = interpolate(
    frame,
    [60, 300],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic)
    }
  );

  // Calculate marker position on curve
  const markerX = 100 + curveProgress * 1300;
  const markerY = 650 - 500 * (1 / (curveProgress * 2 + 0.3));

  // Prompt size (large at start, small at end)
  const promptScale = interpolate(
    curveProgress,
    [0, 1],
    [1, 0.3]
  );

  // Number of test walls
  const wallCount = Math.floor(interpolate(
    curveProgress,
    [0, 1],
    [2, 25]
  ));

  // Final pulse effect
  const finalPulse = frame > 300 ?
    1 + Math.sin((frame - 300) * 0.1) * 0.05 : 1;

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Graph from 4.4 */}
      <PrecisionGraphStatic />

      {/* Marker on curve */}
      <CurveMarker
        x={markerX}
        y={markerY}
        progress={curveProgress}
      />

      {/* Prompt size indicator */}
      <PromptIcon
        scale={promptScale * finalPulse}
        position={{ x: 250, y: 400 }}
      />

      {/* Test walls */}
      <TestWalls
        count={wallCount}
        position={{ x: 1200, y: 400 }}
        scale={finalPulse}
      />

      {/* Position labels */}
      <PositionLabel
        text="FEW TESTS"
        position="left"
        active={curveProgress < 0.3}
      />
      <PositionLabel
        text="MANY TESTS"
        position="right"
        active={curveProgress > 0.7}
      />
    </AbsoluteFill>
  );
};
```

### Curve Marker Component

```typescript
const CurveMarker: React.FC<{
  x: number;
  y: number;
  progress: number;
}> = ({ x, y, progress }) => {
  // Trail effect
  const trailPoints = [];
  for (let i = 0; i < 10; i++) {
    const trailProgress = Math.max(0, progress - i * 0.02);
    const trailX = 100 + trailProgress * 1300;
    const trailY = 650 - 500 * (1 / (trailProgress * 2 + 0.3));
    trailPoints.push({ x: trailX, y: trailY, opacity: 1 - i * 0.1 });
  }

  return (
    <svg style={{
      position: 'absolute',
      width: '100%',
      height: '100%'
    }}>
      {/* Trail */}
      {trailPoints.map((point, i) => (
        <circle
          key={i}
          cx={point.x}
          cy={point.y}
          r={4}
          fill={`rgba(255, 255, 255, ${point.opacity * 0.3})`}
        />
      ))}

      {/* Main marker */}
      <circle
        cx={x}
        cy={y}
        r={12}
        fill="white"
        filter="url(#markerGlow)"
      />

      <defs>
        <filter id="markerGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur"/>
          <feMerge>
            <feMergeNode in="blur"/>
            <feMergeNode in="SourceGraphic"/>
          </feMerge>
        </filter>
      </defs>
    </svg>
  );
};
```

### Prompt Icon Component

```typescript
const PromptIcon: React.FC<{
  scale: number;
  position: { x: number; y: number };
}> = ({ scale, position }) => {
  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      transform: `scale(${scale})`,
      transformOrigin: 'center',
    }}>
      <div style={{
        width: 200,
        height: 250,
        backgroundColor: '#4A90D9',
        borderRadius: 8,
        display: 'flex',
        flexDirection: 'column',
        padding: 15,
        boxShadow: '0 0 30px rgba(74, 144, 217, 0.5)',
      }}>
        {/* File header */}
        <div style={{
          fontSize: 14,
          color: 'rgba(255, 255, 255, 0.7)',
          marginBottom: 10,
        }}>
          parser.prompt
        </div>

        {/* Prompt lines */}
        {[...Array(8)].map((_, i) => (
          <div key={i} style={{
            height: 8,
            backgroundColor: 'rgba(255, 255, 255, 0.3)',
            marginBottom: 6,
            borderRadius: 4,
            width: `${60 + Math.random() * 30}%`,
          }} />
        ))}
      </div>
    </div>
  );
};
```

### Test Walls Component

```typescript
const TestWalls: React.FC<{
  count: number;
  position: { x: number; y: number };
  scale: number;
}> = ({ count, position, scale }) => {
  const walls = [...Array(count)].map((_, i) => ({
    x: (i % 5) * 35,
    y: Math.floor(i / 5) * 45,
    key: i,
  }));

  return (
    <div style={{
      position: 'absolute',
      left: position.x,
      top: position.y,
      transform: `scale(${scale})`,
      transformOrigin: 'center',
    }}>
      {walls.map(wall => (
        <div key={wall.key} style={{
          position: 'absolute',
          left: wall.x,
          top: wall.y,
          width: 25,
          height: 35,
          backgroundColor: '#D9944A',
          borderRadius: 4,
          boxShadow: '0 0 15px rgba(217, 148, 74, 0.5)',
        }} />
      ))}
    </div>
  );
};
```

### Easing

- Marker movement: `easeInOutCubic` (smooth, mathematical)
- Prompt scale: Linear (tied to marker)
- Wall multiplication: Step function tied to marker
- Final pulse: `easeInOutSine`

## Narration Sync

> "With few tests, your prompt needs to specify everything. Edge cases. Error handling. Exact behavior in every situation."
>
> "With many tests, the prompt only needs to specify intent. The tests handle the constraints."

The marker moves from left to right as the narration contrasts few vs many tests.

## Audio Notes

- Soft "whoosh" as marker travels
- Subtle clicks as walls appear
- Pitch rises slightly as tests increase
- Satisfying resolution at end

## Visual Style Notes

- Marker trail adds motion blur effect
- Prompt and walls should feel balanced visually
- The transformation should be gradual and satisfying
- 3Blue1Brown-style mathematical animation

## Transition

Cuts to Section 4.6 showing the long prompt in detail.
