# Section 5.2: Patching Curve -- Linear, Local Returns

**Tool:** Remotion
**Duration:** ~20 seconds
**Timestamp:** 18:10 - 18:30

## Visual Description

The patching curve (amber) draws out across the full graph. Each patch is visualized as a discrete dot along the curve -- a point of investment. The return for each is local: one bug fixed in one place. The curve grows linearly at first, then begins to flatten as patches interact badly, showing the diminishing-returns nature of patching. Small callout annotations appear near individual dots: "one bug fixed", "local return only".

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continues from Section 5.1 graph (axes, labels, legend already visible)

### Animation Elements

1. **Patching Curve (Full Draw)**
   - Color: Amber (#D9944A)
   - Stroke width: 3px
   - Starts linear (steady positive slope)
   - Begins to flatten around the 60-70% mark of X-axis
   - Mathematical form: `y = a * log(x + 1)` (logarithmic -- fast early, diminishing)

2. **Patch Dots**
   - Small circles (8px radius) along the curve at regular intervals
   - Color: Amber (#D9944A) with white border
   - Each dot represents one patch / point of investment
   - 12-15 dots total, evenly spaced along X-axis
   - Dots appear sequentially as the curve draws

3. **Callout Annotations**
   - Near dot #3: "one bug fixed" (small, italic, white at 70% opacity)
   - Near dot #6: "local return only" (small, italic, white at 70% opacity)
   - Thin leader lines from annotation text to the dots
   - Annotations fade in after their respective dots appear

4. **Flattening Indicator**
   - As the curve begins to flatten, the spacing between dots' Y-values visibly decreases
   - A subtle dashed horizontal guide line at the flattening level suggests a ceiling

5. **PDD Curve (Dormant)**
   - The PDD curve from 5.1 remains visible at its starting segment
   - Slight blue glow to remind viewer it exists
   - Not growing yet -- will be the focus of 5.4

### Visual Design

```
+----------------------------------------------+
|                                               |
|  Cumulative       [Patching] ----  (amber)    |
|  Value of         [PDD]      ----  (blue)     |
|  Investment                                   |
|      ^      - - - - - - - - - - ceiling? - -  |
|      |                    .o...o...o...o       |
|      |               .o'                      |
|      |           .o'    "local return only"    |
|      |       .o'                              |
|      |   .o'   "one bug fixed"                |
|      | o'                                     |
|      +--------------------------------------+ |
|                     Time                      |
+----------------------------------------------+
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Curve draws from where 5.1 left off to ~40% of X-axis
   - Linear growth phase
   - Dots #1-5 appear sequentially along the curve
   - Each dot appears with a small "pop" (scale 0 -> 1)

2. **Frame 90-150 (3-5s):** First annotation appears
   - "one bug fixed" callout near dot #3
   - Leader line draws from text to dot
   - Subtle fade-in

3. **Frame 150-330 (5-11s):** Curve continues drawing to ~75% of X-axis
   - Slope starts visibly decreasing (transition from linear to sublinear)
   - Dots #6-10 appear, but vertical spacing between them shrinks
   - Second annotation: "local return only" near dot #6

4. **Frame 330-450 (11-15s):** Curve flattens noticeably
   - Dots #11-14 appear with clearly diminished vertical gains
   - Dashed ceiling guide line fades in subtly
   - The "each patch has local returns" message is visually clear

5. **Frame 450-600 (15-20s):** Hold on complete patching curve
   - All elements visible
   - The flattening is the visual emphasis
   - PDD curve's starting segment pulses faintly (foreshadowing)

### Code Structure (Remotion)

```typescript
const PatchingCurve: React.FC = () => {
  const frame = useCurrentFrame();

  // Curve draw progress (logarithmic shape)
  const curveProgress = interpolate(
    frame,
    [0, 450],
    [0.08, 1],
    { extrapolateRight: 'clamp' }
  );

  // Generate patch dots based on curve progress
  const visibleDots = Math.floor(
    interpolate(
      frame,
      [0, 450],
      [1, 14],
      { extrapolateRight: 'clamp' }
    )
  );

  // Annotation opacities
  const annotation1Opacity = interpolate(
    frame,
    [90, 150],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const annotation2Opacity = interpolate(
    frame,
    [150, 210],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Ceiling line opacity
  const ceilingOpacity = interpolate(
    frame,
    [330, 420],
    [0, 0.4],
    { extrapolateRight: 'clamp' }
  );

  // Logarithmic curve function
  const patchingY = (t: number) => {
    const maxHeight = 550;
    return maxHeight * Math.log(t * 5 + 1) / Math.log(6);
  };

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      {/* Existing axes, labels, legend from 5.1 */}
      <CompoundGraphFrame />

      {/* Patching curve */}
      <LogarithmicCurve
        progress={curveProgress}
        color="#D9944A"
        strokeWidth={3}
        yFunction={patchingY}
      />

      {/* Patch dots */}
      {Array.from({ length: visibleDots }).map((_, i) => (
        <PatchDot
          key={i}
          index={i}
          totalDots={14}
          yFunction={patchingY}
          color="#D9944A"
        />
      ))}

      {/* Annotations */}
      <CurveAnnotation
        text="one bug fixed"
        dotIndex={2}
        opacity={annotation1Opacity}
        yFunction={patchingY}
      />
      <CurveAnnotation
        text="local return only"
        dotIndex={5}
        opacity={annotation2Opacity}
        yFunction={patchingY}
      />

      {/* Ceiling guide */}
      <DashedHorizontalLine
        y={patchingY(1)}
        opacity={ceilingOpacity}
      />

      {/* PDD curve dormant glow */}
      <CompoundCurve
        type="pdd"
        progress={0.08}
        color="#4A90D9"
        glowPulse={frame > 450}
      />
    </AbsoluteFill>
  );
};
```

### Easing

- Curve draw: `easeOutQuad` (decelerating -- mirrors the sublinear growth)
- Dot pop-in: `spring({ damping: 12, stiffness: 200 })`
- Annotation fade: `easeOutCubic`
- Ceiling line: `easeOutQuad`

## Narration Sync

> "When you patch code, each fix has local returns. You fixed one bug in one place. Similar bugs can still occur elsewhere. And sometimes your patch introduces new bugs -- CodeRabbit found AI patches carry one-point-seven times more issues than human code. So each patch risks creating more patches."

- "each fix has local returns" -- dot #3 annotation appears ("one bug fixed")
- "Similar bugs can still occur elsewhere" -- the curve's flattening becomes visible
- "introduces new bugs" -- foreshadows the wobbles in 5.3
- "risks creating more patches" -- curve is clearly sublinear by end of narration

## Audio Notes

- Subtle "pop" sound for each dot appearing (quiet, rhythmic)
- Low tone that subtly drops in pitch as the curve flattens
- No dramatic stings -- this is the setup, not the payoff

## Visual Style Notes

- The dots along the curve are important -- they make "each patch is a point of investment" concrete
- The flattening should feel inevitable, not sudden
- Logarithmic curve is the mathematical model: `y = a * log(x + 1)`
- Keep the PDD curve visible but subdued -- the viewer should be aware of it but not distracted

## Transition

Continues directly into Section 5.3 where the patching curve wobbles with regressions and conflicts.
