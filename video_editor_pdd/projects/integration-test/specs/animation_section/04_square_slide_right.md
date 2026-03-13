[Remotion]

# Section 1.4: Square Slide Right

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:03.7 - 0:04.7

## Visual Description
The indigo rounded square from the previous morph slides from center to the right side of the canvas. The square translates horizontally from x=960 to x=1440 while leaving a horizontal motion streak behind it. The streak is a gradient bar that fades from the shape's color to transparent, trailing 200px behind the shape. As the square reaches its destination, it performs a small bounce (overshoot by 20px, then settle).

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Charcoal #1E293B with radial gradient to #0F172A at edges
- Grid lines: None

### Chart/Visual Elements
- Square: 120x120px, borderRadius 12px, fill #6366F1 (indigo)
- Start position: centered at (960, 540)
- End position: (1440, 540)
- Motion streak: horizontal gradient bar, height 120px, trailing the square, from #6366F1 at 30% opacity to transparent
- Streak length: up to 200px

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** Anticipation — square shifts 10px left (to 950)
2. **Frame 3-21 (0.1-0.7s):** Square slides from x=950 to x=1460 (overshoot); motion streak visible
3. **Frame 21-27 (0.7-0.9s):** Bounce back from x=1460 to x=1440; streak fades
4. **Frame 27-30 (0.9-1.0s):** Settle at x=1440, streak fully faded

### Typography
- None

### Easing
- Anticipation: `easeInQuad`
- Main slide: `easeOutCubic`
- Bounce settle: `easeOutBounce`
- Streak fade: `easeOutQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <SlideWithStreak
    fromX={960}
    toX={1440}
    overshoot={20}
    shape={<RoundedSquare size={120} radius={12} color="#6366F1" />}
  />
</Sequence>
```

## Data Points
```json
{
  "slide": {
    "fromX": 960,
    "toX": 1440,
    "y": 540,
    "overshoot": 20,
    "streakLength": 200
  }
}
```

---
