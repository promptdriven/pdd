# Section 1.2: The Threshold Highlight

**Tool:** Remotion
**Duration:** ~10 seconds
**Timestamp:** 2:20 - 2:30

## Visual Description

The crossing point from the previous chart gets highlighted with a pulsing effect and label. This is the key moment where darning became economically irrational.

## Technical Specifications

### Canvas
- Continues from Section 1.1 chart
- Same dark background and grid

### Animation Elements

1. **Crossing Point Marker**
   - Circle at intersection (~1963, ~0.5 hours)
   - Color: White (#FFFFFF)
   - Size: Starts at 0, grows to 20px radius
   - Pulsing glow effect (amber #D9944A at 50% opacity)

2. **Label: "The Threshold"**
   - Position: Above and right of crossing point
   - Font: Sans-serif bold, 24pt
   - Color: White
   - Connector line from label to point

3. **Highlight Effect**
   - Radial gradient pulse emanating from crossing point
   - 3 pulses, each fading out
   - Color: Amber gradient fading to transparent

### Animation Sequence

1. **Frame 0-30 (0-1s):** Circle marker grows in (scale 0 → 1)
2. **Frame 30-90 (1-3s):** Pulse effect begins, first wave
3. **Frame 60-120 (2-4s):** Label fades in with connector line
4. **Frame 90-150 (3-5s):** Second pulse wave
5. **Frame 150-210 (5-7s):** Third pulse wave
6. **Frame 210-300 (7-10s):** Hold, pulses continue subtly

### Easing
- Circle growth: `spring({ damping: 15 })`
- Pulse waves: `easeOutQuad` with opacity decay
- Label fade: `easeOutCubic`

## Narration Sync

> "Darning made sense. You'd spend thirty minutes to save a dollar."

## Code Structure (Remotion)

```typescript
<Sequence from={0} durationInFrames={300}>
  {/* Inherit chart from previous section */}
  <PreviousChart frozen />

  <Sequence from={0}>
    <CrossingPointMarker
      x={crossingX}
      y={crossingY}
      pulseColor="#D9944A"
    />
  </Sequence>

  <Sequence from={60}>
    <AnimatedLabel
      text="The Threshold"
      position={{ x: crossingX + 50, y: crossingY - 40 }}
    />
    <ConnectorLine from={labelPosition} to={crossingPoint} />
  </Sequence>
</Sequence>
```

## Visual Style Notes

- The pulse effect should feel significant but not overwhelming
- 3Blue1Brown style: clean, mathematical, satisfying
- The glow should draw the eye without being garish

## Transition

After the threshold is established, the chart will continue animating forward in time (Section 1.3).
