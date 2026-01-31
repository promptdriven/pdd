# Section 4.4: Precision Graph Introduction

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 14:30 - 14:45

## Visual Description

A graph appears showing the inverse relationship between test count and required prompt precision. X-axis: "Number of Tests", Y-axis: "Required Prompt Precision". An inverse curve forms, illustrating that more tests mean simpler prompts.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Centered graph composition

### Animation Elements

1. **Axes**
   - X-axis: "Number of Tests" (left to right: 0 → Many)
   - Y-axis: "Required Prompt Precision" (bottom to top: Low → High)
   - Clean, minimal styling
   - White/light gray lines

2. **Inverse Curve**
   - Starts high-left (few tests, high precision)
   - Curves down to low-right (many tests, low precision)
   - Gradient from Blue (#4A90D9) to Amber (#D9944A)
   - Smooth, mathematical curve

3. **Axis Labels**
   - Clear typography
   - Fade in with axes
   - Sans-serif font

4. **Region Labels** (optional)
   - "FEW TESTS" on left side
   - "MANY TESTS" on right side
   - Subtle, contextual

### Visual Design

```
┌────────────────────────────────────┐
│                                    │
│  Required                          │
│  Prompt    ●──.                    │
│  Precision     `-.                 │
│      ↑            `-.              │
│      │                `-.          │
│      │                   `-.       │
│      │                      `──●   │
│      │                             │
│      └──────────────────────────→  │
│                Number of Tests     │
│                                    │
│     [Blue]        →       [Amber]  │
└────────────────────────────────────┘
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Axes appear
   - Y-axis draws from origin upward
   - X-axis draws from origin rightward
   - Clean line animation

2. **Frame 60-120 (2-4s):** Labels fade in
   - "Required Prompt Precision" on Y-axis
   - "Number of Tests" on X-axis
   - Subtle fade-in animation

3. **Frame 120-270 (4-9s):** Curve draws
   - Curve draws from left to right
   - Color transitions from blue to amber
   - Smooth, satisfying draw animation

4. **Frame 270-450 (9-15s):** Hold on complete graph
   - All elements visible
   - Subtle glow on curve
   - Ready for narration completion

### Code Structure (Remotion)

```typescript
const PrecisionGraph: React.FC = () => {
  const frame = useCurrentFrame();

  // Axis draw progress
  const yAxisProgress = interpolate(
    frame,
    [0, 60],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const xAxisProgress = interpolate(
    frame,
    [20, 80],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Label opacity
  const labelOpacity = interpolate(
    frame,
    [60, 120],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Curve draw progress
  const curveProgress = interpolate(
    frame,
    [120, 270],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Graph container */}
      <div style={{
        position: 'absolute',
        left: 200,
        top: 100,
        width: 1520,
        height: 800
      }}>
        {/* Axes */}
        <GraphAxes
          yProgress={yAxisProgress}
          xProgress={xAxisProgress}
        />

        {/* Labels */}
        <AxisLabels opacity={labelOpacity} />

        {/* Inverse curve */}
        <InverseCurve progress={curveProgress} />
      </div>
    </AbsoluteFill>
  );
};
```

### Graph Axes Component

```typescript
const GraphAxes: React.FC<{
  yProgress: number;
  xProgress: number;
}> = ({ yProgress, xProgress }) => {
  const ORIGIN = { x: 100, y: 650 };
  const Y_END = { x: 100, y: 50 };
  const X_END = { x: 1400, y: 650 };

  return (
    <svg style={{
      position: 'absolute',
      width: '100%',
      height: '100%'
    }}>
      {/* Y-axis */}
      <line
        x1={ORIGIN.x}
        y1={ORIGIN.y}
        x2={ORIGIN.x}
        y2={ORIGIN.y - (ORIGIN.y - Y_END.y) * yProgress}
        stroke="rgba(255, 255, 255, 0.8)"
        strokeWidth={2}
      />

      {/* Y-axis arrow */}
      {yProgress === 1 && (
        <polygon
          points={`${Y_END.x},${Y_END.y} ${Y_END.x-8},${Y_END.y+16} ${Y_END.x+8},${Y_END.y+16}`}
          fill="rgba(255, 255, 255, 0.8)"
        />
      )}

      {/* X-axis */}
      <line
        x1={ORIGIN.x}
        y1={ORIGIN.y}
        x2={ORIGIN.x + (X_END.x - ORIGIN.x) * xProgress}
        y2={ORIGIN.y}
        stroke="rgba(255, 255, 255, 0.8)"
        strokeWidth={2}
      />

      {/* X-axis arrow */}
      {xProgress === 1 && (
        <polygon
          points={`${X_END.x},${X_END.y} ${X_END.x-16},${X_END.y-8} ${X_END.x-16},${X_END.y+8}`}
          fill="rgba(255, 255, 255, 0.8)"
        />
      )}
    </svg>
  );
};
```

### Inverse Curve Component

```typescript
const InverseCurve: React.FC<{ progress: number }> = ({ progress }) => {
  // Generate curve points
  const generateCurvePath = () => {
    const points: string[] = [];
    const numPoints = 100;

    for (let i = 0; i <= numPoints * progress; i++) {
      const t = i / numPoints;
      const x = 100 + t * 1300;
      // Inverse function: y = 1 / (x + 0.2) normalized
      const y = 650 - 500 * (1 / (t * 2 + 0.3));

      if (i === 0) {
        points.push(`M ${x} ${y}`);
      } else {
        points.push(`L ${x} ${y}`);
      }
    }

    return points.join(' ');
  };

  return (
    <svg style={{
      position: 'absolute',
      width: '100%',
      height: '100%'
    }}>
      <defs>
        <linearGradient id="curveGradient" x1="0%" y1="0%" x2="100%" y2="0%">
          <stop offset="0%" stopColor="#4A90D9" />
          <stop offset="100%" stopColor="#D9944A" />
        </linearGradient>

        <filter id="curveGlow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="4" result="coloredBlur"/>
          <feMerge>
            <feMergeNode in="coloredBlur"/>
            <feMergeNode in="SourceGraphic"/>
          </feMerge>
        </filter>
      </defs>

      <path
        d={generateCurvePath()}
        fill="none"
        stroke="url(#curveGradient)"
        strokeWidth={4}
        strokeLinecap="round"
        filter="url(#curveGlow)"
      />
    </svg>
  );
};
```

### Axis Labels Component

```typescript
const AxisLabels: React.FC<{ opacity: number }> = ({ opacity }) => {
  return (
    <>
      {/* Y-axis label */}
      <div style={{
        position: 'absolute',
        left: -80,
        top: 350,
        transform: 'rotate(-90deg)',
        transformOrigin: 'center',
        color: 'rgba(255, 255, 255, 0.9)',
        fontSize: 24,
        fontFamily: 'system-ui, sans-serif',
        opacity,
        whiteSpace: 'nowrap'
      }}>
        Required Prompt Precision
      </div>

      {/* X-axis label */}
      <div style={{
        position: 'absolute',
        left: 700,
        bottom: 20,
        color: 'rgba(255, 255, 255, 0.9)',
        fontSize: 24,
        fontFamily: 'system-ui, sans-serif',
        opacity
      }}>
        Number of Tests
      </div>
    </>
  );
};
```

### Easing

- Axis draw: `easeOutCubic`
- Label fade: `easeOutQuad`
- Curve draw: `easeInOutCubic` (smooth, mathematical feel)

## Narration Sync

> "This maps directly to PDD."

The graph appears as "maps directly" is spoken, visually representing the mapping.

## Audio Notes

- Soft "whoosh" as axes draw
- Subtle mathematical/digital tone as curve draws
- Clean, precise audio aesthetic

## Visual Style Notes

- Mathematical, 3Blue1Brown-style graph
- Clean typography
- Gradient curve is the hero element
- Dark background emphasizes the bright curve

## Transition

Continues directly into Section 4.5 where we animate along the curve showing the tradeoff.
