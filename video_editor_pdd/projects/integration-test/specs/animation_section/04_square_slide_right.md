[Remotion]

# Section 1.4: Green Square Slide Right

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:10 - 0:13

## Visual Description
The green square from the morph transition slides smoothly from center to the right side of the screen, leaving a fading motion trail behind it. As it slides, a subtle dotted guide line appears along the horizontal center axis, reinforcing the movement direction. The square comes to rest at the right-third position.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Charcoal (#141921)
- Grid lines: Dotted horizontal center line, #FFFFFF at 10% opacity, 1px dashed

### Chart/Visual Elements
- Square: 160px, solid fill #22C55E, starts centered at x=640, ends at x=920
- Motion trail: 4 ghost copies of the square at 15%, 10%, 6%, 3% opacity, spaced 40px apart behind the square, each delayed by 3 frames
- Guide line: Horizontal dashed line at y=360, spans full width, appears during slide

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Green square holds at center. Guide line fades in from 0% to 10% opacity.
2. **Frame 10-60 (0.33-2.0s):** Square translates x from 640 → 920. Motion trail ghosts follow with staggered delay. Guide line is visible throughout.
3. **Frame 60-75 (2.0-2.5s):** Square arrives at x=920 with slight overshoot (x=935) then settles back to 920. Trail ghosts catch up and fade out.
4. **Frame 75-90 (2.5-3.0s):** Square rests at final position. Guide line fades out. Soft green glow appears behind square.

### Typography
- None

### Easing
- Slide translation: `easeInOutCubic`
- Overshoot settle: `spring({ damping: 10, stiffness: 160 })`
- Trail fade: `easeOutQuad`
- Guide line fade: `easeInOutSine`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: '#141921' }}>
    <GuideLine axis="horizontal" y={360} fadeIn={0} fadeOut={75} />
    <MotionTrail
      count={4}
      opacities={[0.15, 0.10, 0.06, 0.03]}
      spacing={40}
      delayFrames={3}
    />
    <SlidingSquare
      size={160}
      color="#22C55E"
      fromX={640}
      toX={920}
      slideStart={10}
      slideEnd={60}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "shape": "square",
  "size": 160,
  "color": "#22C55E",
  "startX": 640,
  "endX": 920,
  "trailCopies": 4,
  "centerY": 360
}
```

---
