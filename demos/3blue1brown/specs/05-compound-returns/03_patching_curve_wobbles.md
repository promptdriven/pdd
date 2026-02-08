# Section 5.3: Patching Curve Wobbles and Dips

**Tool:** Remotion
**Duration:** ~15 seconds
**Timestamp:** 18:30 - 18:45

## Visual Description

The patching curve (amber) from Section 5.2 now wobbles and occasionally dips as patches interact badly. Small annotations appear at the dip points: "new bug from patch", "regression", "merge conflict". The curve's overall trajectory is sublinear -- it still trends upward, but the dips make the net progress even worse than a smooth logarithmic curve. The visual message is clear: patching returns are linear at best, often sublinear, and plagued by setbacks.

## Technical Specifications

### Canvas
- Resolution: 1920x1080
- Background: Dark (#1a1a2e)
- Continues from Section 5.2 (full patching curve visible with dots)

### Animation Elements

1. **Wobble Animation on Existing Curve**
   - The smooth logarithmic curve from 5.2 morphs into a wobbly version
   - 3-4 distinct dips along the latter half of the curve
   - Dips are 10-20% of the curve's height at that point
   - Between dips, the curve resumes climbing but at reduced slope

2. **Dip Annotations**
   - Dip 1 (~55% along X): "new bug from patch"
     - Color: Red-tinted amber (#E06040)
     - Small downward arrow icon beside text
   - Dip 2 (~70% along X): "regression"
     - Color: Red-tinted amber (#E06040)
     - Small circular "revert" icon
   - Dip 3 (~85% along X): "merge conflict"
     - Color: Red-tinted amber (#E06040)
     - Small forking-paths icon
   - All annotations are small (16pt), italic, positioned just below their dip points
   - Thin red-tinted leader lines connect annotations to dip troughs

3. **Flicker/Shake Effect at Dips**
   - At each dip, the curve segment briefly flickers or shakes laterally (1-2px)
   - Suggests instability and fragility
   - Duration: 5-8 frames per flicker

4. **Cost Statistic Callout**
   - After the third dip, a larger callout fades in at upper-right:
   - "$1.52T" in large text (36pt, bold, red-amber #E06040)
   - "annual US tech debt cost (CISQ)" in smaller text (18pt, white at 70% opacity)
   - Subtle background card with dark border

5. **PDD Curve (Still Dormant)**
   - PDD starting segment remains visible, unchanged
   - Faint blue glow continues

### Visual Design

```
+----------------------------------------------+
|                                     $1.52T    |
|  Cumulative       [Patching]        annual    |
|  Value of         [PDD]             debt cost |
|  Investment                                   |
|      ^                .o~v~o..o               |
|      |            .o'v     "merge conflict"   |
|      |        .o'  "regression"               |
|      |    .o'v                                |
|      |  .o' "new bug from patch"              |
|      | o'                                     |
|      +--------------------------------------+ |
|                     Time                      |
+----------------------------------------------+
```

### Animation Sequence

1. **Frame 0-90 (0-3s):** Curve morphs from smooth to wobbly
   - The smooth logarithmic curve from 5.2 progressively deforms
   - First dip appears at ~55% mark
   - Curve flickers at dip point
   - "new bug from patch" annotation fades in

2. **Frame 90-180 (3-6s):** Second dip appears
   - Curve dips at ~70% mark
   - Flicker effect
   - "regression" annotation fades in
   - The recovery slope after this dip is shallower than before

3. **Frame 180-270 (6-9s):** Third dip appears
   - Curve dips at ~85% mark
   - Flicker effect
   - "merge conflict" annotation fades in
   - By now the curve is nearly flat with visible damage

4. **Frame 270-360 (9-12s):** Cost statistic callout
   - "$1.52T" fades in at upper-right
   - "annual US tech debt cost (CISQ)" subtitle appears
   - The number's size and color draw the eye

5. **Frame 360-450 (12-15s):** Hold on damaged curve
   - All dips, annotations, and the cost callout visible
   - The contrast with the still-dormant PDD curve is stark
   - The patching curve looks battered and stalled

### Code Structure (Remotion)

```typescript
const PatchingCurveWobbles: React.FC = () => {
  const frame = useCurrentFrame();

  // Wobble morph progress (smooth -> wobbly)
  const wobbleProgress = interpolate(
    frame,
    [0, 270],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  // Dip visibility
  const dip1Active = frame >= 30;
  const dip2Active = frame >= 120;
  const dip3Active = frame >= 210;

  // Annotation opacities
  const annot1Opacity = interpolate(frame, [60, 90], [0, 1], { extrapolateRight: 'clamp' });
  const annot2Opacity = interpolate(frame, [150, 180], [0, 1], { extrapolateRight: 'clamp' });
  const annot3Opacity = interpolate(frame, [240, 270], [0, 1], { extrapolateRight: 'clamp' });

  // Cost callout opacity
  const costOpacity = interpolate(frame, [270, 330], [0, 1], { extrapolateRight: 'clamp' });

  // Flicker effect at dip points
  const flickerOffset = (dipFrame: number) => {
    const localFrame = frame - dipFrame;
    if (localFrame < 0 || localFrame > 8) return 0;
    return Math.sin(localFrame * Math.PI * 2) * 2;
  };

  // Wobbly patching curve with dips
  const wobblePatchingY = (t: number, wobbleAmount: number) => {
    const baseY = 550 * Math.log(t * 5 + 1) / Math.log(6);
    // Add dips at specific positions
    const dip1 = dip1Active ? -60 * Math.exp(-Math.pow((t - 0.55) / 0.04, 2)) : 0;
    const dip2 = dip2Active ? -45 * Math.exp(-Math.pow((t - 0.70) / 0.04, 2)) : 0;
    const dip3 = dip3Active ? -50 * Math.exp(-Math.pow((t - 0.85) / 0.04, 2)) : 0;
    return baseY + (dip1 + dip2 + dip3) * wobbleAmount;
  };

  return (
    <AbsoluteFill style={{ backgroundColor: '#1a1a2e' }}>
      <CompoundGraphFrame />

      {/* Wobbly patching curve */}
      <WobblyCurve
        progress={1}
        wobbleAmount={wobbleProgress}
        color="#D9944A"
        strokeWidth={3}
        yFunction={(t) => wobblePatchingY(t, wobbleProgress)}
        flickerOffset={flickerOffset}
      />

      {/* Dip annotations */}
      <DipAnnotation
        text="new bug from patch"
        xPosition={0.55}
        opacity={annot1Opacity}
        color="#E06040"
        icon="arrow-down"
      />
      <DipAnnotation
        text="regression"
        xPosition={0.70}
        opacity={annot2Opacity}
        color="#E06040"
        icon="revert"
      />
      <DipAnnotation
        text="merge conflict"
        xPosition={0.85}
        opacity={annot3Opacity}
        color="#E06040"
        icon="fork"
      />

      {/* Cost statistic callout */}
      <StatCallout
        value="$1.52T"
        subtitle="annual US tech debt cost (CISQ)"
        opacity={costOpacity}
        position={{ x: 1200, y: 120 }}
        valueColor="#E06040"
      />

      {/* PDD curve dormant */}
      <CompoundCurve
        type="pdd"
        progress={0.08}
        color="#4A90D9"
        glowPulse={true}
      />
    </AbsoluteFill>
  );
};
```

### Easing

- Wobble morph: `easeInOutQuad` (gradual degradation)
- Dip appearance: `easeOutCubic` with slight bounce
- Annotation fade: `easeOutQuad`
- Cost callout: `easeOutCubic`
- Flicker: Linear sinusoidal (raw, unstable feel)

## Narration Sync

> "The returns are linear at best. Often sublinear. And the cost keeps compounding -- CISQ estimates technical debt costs US companies one-point-five-two trillion dollars annually."

- "linear at best" -- the curve's sublinear shape is already clear
- "Often sublinear" -- the dips are visible, annotations pointing to regressions
- "one-point-five-two trillion" -- the "$1.52T" callout appears, landing the statistic visually

## Audio Notes

- Subtle "thud" or low-frequency impact at each dip (suggests something breaking)
- Very quiet static/crackle during flicker moments
- When "$1.52T" appears: a brief, resonant low tone (weight of the number)
- Contrast with the clean, mathematical sounds of the axis setup

## Visual Style Notes

- The dips should feel organic and disruptive, not mechanical
- Red-amber tint (#E06040) on annotations signals danger/cost without being garish
- The "$1.52T" is the emotional anchor of this section -- it should be the largest, most prominent text element
- The flicker effect is subtle -- 1-2 pixels of lateral shake, not dramatic screen shake
- The overall mood shifts from "the curve is just flattening" (5.2) to "the curve is actively damaged" (5.3)

## Transition

Continues directly into Section 5.4 where the PDD curve is introduced and begins its contrasting growth.
