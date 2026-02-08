# Section 5.1: Compound Curves Introduction

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 18:00 - 18:10

## Visual Description

A graph appears with two labeled curves. One is labeled "Patching" (amber), one is labeled "PDD" (blue). The X-axis is labeled "Time" and the Y-axis is labeled "Cumulative Value of Investment". Both curves are shown in their initial state -- just the axes, labels, and the first hint of both curves beginning from the origin. This establishes the frame that will be built upon in the following sections.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Centered graph composition with generous margins

### Animation Elements

1. **Axes**
   - X-axis: "Time" (left to right)
   - Y-axis: "Cumulative Value of Investment" (bottom to top)
   - Clean, minimal white/light gray lines (rgba(255, 255, 255, 0.8))
   - Arrowheads at axis ends
   - Origin at bottom-left of graph area

2. **Axis Labels**
   - "Time" below X-axis, centered
   - "Cumulative Value of Investment" rotated along Y-axis
   - Sans-serif font, 24pt, white with 90% opacity

3. **Curve Labels (Legend)**
   - "Patching" with amber (#D9944A) swatch, positioned upper-left of graph area
   - "PDD" with blue (#4A90D9) swatch, positioned below "Patching"
   - Clean legend box with subtle border

4. **Curve Starting Points**
   - Both curves begin at the origin
   - Only the very beginning of each curve is visible (first 5-10% of X range)
   - Both start at similar slopes to set up the divergence to come

### Visual Design

```
+----------------------------------------------+
|                                               |
|  Cumulative       [Patching] ----  (amber)    |
|  Value of         [PDD]      ----  (blue)     |
|  Investment                                   |
|      ^                                        |
|      |                                        |
|      |                                        |
|      |                                        |
|      | ./                                     |
|      |/                                       |
|      +--------------------------------------+ |
|                     Time                      |
+----------------------------------------------+
```

### Animation Sequence

1. **Frame 0-60 (0-2s):** Axes draw in
   - Y-axis draws upward from origin
   - X-axis draws rightward from origin
   - Arrowheads appear at ends

2. **Frame 60-120 (2-4s):** Labels and legend fade in
   - "Cumulative Value of Investment" on Y-axis
   - "Time" on X-axis
   - Legend box with both curve names and color swatches

3. **Frame 120-210 (4-7s):** Both curves begin drawing from origin
   - Patching curve (amber) starts with moderate positive slope
   - PDD curve (blue) starts with similar moderate positive slope
   - Both are nearly overlapping at this early stage

4. **Frame 210-300 (7-10s):** Hold on initial state
   - Both curves visible but short
   - Viewer registers the setup: two investment strategies, same starting point

### Code Structure (Remotion)

```typescript
const CompoundCurvesIntro: React.FC = () => {
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
    [15, 75],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Label and legend opacity
  const labelOpacity = interpolate(
    frame,
    [60, 120],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Initial curve draw (just the first segment)
  const curveStartProgress = interpolate(
    frame,
    [120, 210],
    [0, 0.08],
    { extrapolateRight: 'clamp' }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <div style={{
        position: 'absolute',
        left: 200,
        top: 80,
        width: 1520,
        height: 850
      }}>
        {/* Axes */}
        <CompoundAxes
          yProgress={yAxisProgress}
          xProgress={xAxisProgress}
        />

        {/* Labels */}
        <CompoundAxisLabels opacity={labelOpacity} />

        {/* Legend */}
        <CurveLegend opacity={labelOpacity} />

        {/* Patching curve (amber, initial segment) */}
        <CompoundCurve
          type="patching"
          progress={curveStartProgress}
          color="#D9944A"
        />

        {/* PDD curve (blue, initial segment) */}
        <CompoundCurve
          type="pdd"
          progress={curveStartProgress}
          color="#4A90D9"
        />
      </div>
    </AbsoluteFill>
  );
};
```

### Easing

- Axis draw: `easeOutCubic`
- Label fade: `easeOutQuad`
- Curve start: `easeInOutCubic` (smooth mathematical feel)

## Narration Sync

> "Let's talk about compound returns."

The axes and labels appear as the narrator speaks. The word "compound" lands as the legend with both curve names becomes visible. The curves just begin to emerge from the origin by the end of the line.

## Audio Notes

- Soft "whoosh" as axes draw in
- Subtle tone shift as legend appears (two-note motif: amber and blue)
- Clean, mathematical aesthetic throughout

## Visual Style Notes

- 3Blue1Brown-style clean graph on dark background
- The initial overlap of both curves is intentional -- they start from the same place
- The legend establishes the color coding (amber = patching, blue = PDD) that will persist through sections 5.1-5.5
- Minimal clutter; let the graph breathe

## Transition

Continues directly into Section 5.2 where the patching curve draws out and its linear/local nature is explained.
