# Section 5.4: PDD Curve -- Compounding Investment

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 18:45 - 18:55

## Visual Description

The PDD curve (blue) now activates and begins drawing forward from its dormant starting segment. Each test added is a dot along the curve -- a point of investment. Unlike the patching dots which had local returns, each PDD dot sends faint radial lines forward along the curve, visually showing that this test constrains all future generations. The curve's slope is increasing (convex), contrasting with the patching curve's decreasing slope (concave).

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continues from Section 5.3 (wobbly patching curve with dips and annotations visible)

### Animation Elements

1. **PDD Curve (Active Draw)**
   - Color: Blue (#4A90D9)
   - Stroke width: 3px
   - Curve draws from the dormant starting segment (~8% of X) out to ~50% of X
   - Shape: Exponential beginning -- `y = a * (e^(bx) - 1)`, convex upward
   - At this stage, the curve is still below or near the patching curve -- the dramatic divergence comes in 5.5
   - Subtle blue glow along the curve (filter: feGaussianBlur, 4px)

2. **Test Dots**
   - Small circles (8px radius) along the PDD curve at regular intervals
   - Color: Blue (#4A90D9) with white border
   - 6-8 dots visible by end of this section
   - Dots appear sequentially as the curve draws

3. **Forward Radial Lines (Key Visual)**
   - When each dot appears, 2-3 faint lines project forward from it along/above the curve
   - Lines are light blue (#6AB0E9) at 30% opacity
   - They extend to the right edge of the graph (representing "all future generations")
   - Each new dot's radial lines overlay with previous ones, creating accumulating density
   - This is the visual metaphor: each test constrains EVERYTHING that comes after

4. **Callout Annotation**
   - Near dot #3: "constrains all future generations"
   - Color: White at 80% opacity, italic, 18pt
   - Leader line to the dot, with the forward radial lines emphasized

5. **Patching Curve (Background)**
   - The wobbly patching curve from 5.3 remains visible but at reduced opacity (60%)
   - Dip annotations remain but dimmed
   - The viewer can compare both curves simultaneously

### Visual Design

```
+----------------------------------------------+
|                                               |
|  Cumulative       [Patching] ----  (amber)    |
|  Value of         [PDD]      ----  (blue)     |
|  Investment                                   |
|      ^                                        |
|      |            ......o--->>>>>>>>>>>>>>>    |
|      |        ...o------>>>>>>>>>>>>>>>>>      |
|      |      .o------>>>>>>>>>>>>>>>>>>>>       |
|      |    o------->>>>>>>>>>>>>>>>>>>>>        |
|      |  o'  "constrains all future gen's"     |
|      | o    [patching curve faded behind]      |
|      +--------------------------------------+ |
|                     Time                      |
+----------------------------------------------+
```

### Animation Sequence

1. **Frame 0-30 (0-1s):** PDD curve activates
   - The dormant blue segment brightens
   - A pulse of light runs along the existing segment
   - The glow intensifies (signals: "now we're looking at this one")

2. **Frame 30-120 (1-4s):** Curve draws forward with first dots
   - Curve extends to ~25% of X-axis
   - Dots #1-3 appear with spring animation
   - Each dot triggers forward radial lines projecting to the right

3. **Frame 120-180 (4-6s):** Annotation appears
   - "constrains all future generations" near dot #3
   - The forward radial lines from this dot pulse brighter briefly
   - Leader line draws from text to dot

4. **Frame 180-240 (6-8s):** More dots, accumulating radial lines
   - Dots #4-6 appear
   - Each adds more forward-projecting lines
   - The density of lines on the right side of the graph increases visibly
   - The cumulative, layered effect shows compounding

5. **Frame 240-300 (8-10s):** Hold with all elements
   - 6-8 dots visible with overlapping forward radial lines
   - The PDD curve is still modest in height but clearly convex (slope increasing)
   - Patching curve visible behind at reduced opacity
   - Stage is set for the exponential divergence in 5.5

### Code Structure (Remotion)

```typescript
const PddCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Activation pulse
  const activationPulse = interpolate(
    frame,
    [0, 30],
    [0.5, 1],
    { extrapolateRight: 'clamp' }
  );

  // Curve draw progress
  const curveProgress = interpolate(
    frame,
    [30, 240],
    [0.08, 0.50],
    { extrapolateRight: 'clamp' }
  );

  // Number of visible dots
  const visibleDots = Math.floor(
    interpolate(frame, [30, 240], [0, 8], { extrapolateRight: 'clamp' })
  );

  // Annotation opacity
  const annotOpacity = interpolate(
    frame,
    [120, 160],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Patching curve background opacity
  const patchingOpacity = interpolate(
    frame,
    [0, 30],
    [1, 0.6],
    { extrapolateRight: 'clamp' }
  );

  // Exponential curve function
  const pddY = (t: number) => {
    const maxHeight = 700;
    return maxHeight * (Math.exp(t * 2.5) - 1) / (Math.exp(2.5) - 1);
  };

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <CompoundGraphFrame />

      {/* Patching curve (dimmed) */}
      <WobblyCurve
        progress={1}
        wobbleAmount={1}
        color="#D9944A"
        strokeWidth={3}
        opacity={patchingOpacity}
      />

      {/* PDD curve */}
      <ExponentialCurve
        progress={curveProgress}
        color="#4A90D9"
        strokeWidth={3}
        yFunction={pddY}
        glowIntensity={activationPulse}
      />

      {/* Test dots with forward radial lines */}
      {Array.from({ length: visibleDots }).map((_, i) => (
        <React.Fragment key={i}>
          <TestDot
            index={i}
            totalDots={8}
            yFunction={pddY}
            color="#4A90D9"
          />
          <ForwardRadialLines
            dotIndex={i}
            totalDots={8}
            yFunction={pddY}
            color="#6AB0E9"
            opacity={0.3}
          />
        </React.Fragment>
      ))}

      {/* Annotation */}
      <CurveAnnotation
        text="constrains all future generations"
        dotIndex={2}
        opacity={annotOpacity}
        yFunction={pddY}
        color="#ffffff"
      />
    </AbsoluteFill>
  );
};
```

### Easing

- Activation pulse: `easeOutQuad`
- Curve draw: `easeInQuad` (accelerating -- mirrors exponential growth)
- Dot appearance: `spring({ damping: 12, stiffness: 200 })`
- Forward radial lines: `easeOutCubic` (quick extension then settle)
- Annotation fade: `easeOutCubic`

## Narration Sync

> "When you add a test in PDD, the returns are different."

- "When you add a test" -- a test dot appears on the PDD curve
- "the returns are different" -- the forward radial lines project outward, making the difference visible
- This is a short, pivotal narration line; the visual of the forward-projecting lines does most of the communication

## Audio Notes

- A clean, ascending tone as the PDD curve activates (contrast with the low thuds of 5.3)
- Each test dot makes a clear, bright "ping" (contrasting with the "pop" of patch dots)
- The forward radial lines have a subtle "shimmer" or sustained harmonic
- The overall audio shifts from the troubled tone of 5.3 to something cleaner and more hopeful

## Visual Style Notes

- The forward radial lines are the key innovation in this visual -- they make "compound returns" concrete
- Keep the lines delicate (30% opacity) so they layer nicely without becoming a mess
- The PDD curve's convex shape (slope increasing) should contrast sharply with the patching curve's concave shape (slope decreasing)
- The blue glow on the PDD curve provides visual warmth and importance
- At this stage, the PDD curve has NOT yet dramatically exceeded the patching curve -- that payoff is in 5.5

## Transition

Continues directly into Section 5.5 where the PDD curve grows exponentially and the gap between curves widens dramatically.
