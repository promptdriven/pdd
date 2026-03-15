[Remotion]

# Section 1.4: Square Slide Right

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:03 - 0:04

## Visual Description
The indigo rounded square (from the morph) performs a dynamic slide to the right side of the screen. The motion begins with a subtle anticipation pull-back to the left, then accelerates rightward with a horizontal stretch squash, overshoots the target position, and bounces back to rest. A horizontal motion streak trails behind the square during peak velocity, adding a sense of speed and energy.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient from center `#0F172A` to edge `#020617`
- Grid lines: None

### Chart/Visual Elements
- **Square:** 130px, border-radius 12px, fill `#6366F1`, starts at X=960, Y=540
- **Motion Streak:** Horizontal bar, `#6366F1` at 40% opacity, 6px tall, max 280px wide
- **Guide Line:** Subtle horizontal reference line (optional, very faint)
- **Glow:** Soft halo around square during motion

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Anticipation — square pulls left 20px (X: 960→940), scaleX compresses to 0.97
2. **Frame 6-20 (0.2-0.67s):** Main slide — square accelerates right (X: 940→1470), scaleX stretches to 1.03 during peak velocity then normalizes. Motion streak visible from frames 10-18
3. **Frame 20-26 (0.67-0.87s):** Bounce back — square overshoots and settles (X: 1470→1440), scale returns to 1.0
4. **Frame 26-30 (0.87-1.0s):** Hold at final position X=1440

### Typography
- None

### Easing
- Anticipation: `easeIn(quad)`
- Main slide: `easeOut(cubic)`
- Bounce back: `easeInOut(sin)`
- Motion streak fade: `linear`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <GuideLine y={540} />
  <MotionStreak
    y={540}
    maxWidth={280}
    height={6}
    color="#6366F1"
    opacity={0.4}
  />
  <SquareGlow />
  <SlidingSquare
    startX={960}
    endX={1440}
    anticipation={20}
    overshoot={30}
    size={130}
    borderRadius={12}
    color="#6366F1"
  />
</Sequence>
```

## Data Points
```json
{
  "startX": 960,
  "endX": 1440,
  "y": 540,
  "anticipationPx": 20,
  "overshootPx": 30,
  "shapeSize": 130,
  "borderRadius": 12,
  "shapeColor": "#6366F1",
  "streakMaxWidth": 280,
  "streakHeight": 6,
  "streakOpacity": 0.4,
  "scaleFactors": {
    "anticipation": 0.97,
    "slideStretch": 1.03,
    "normal": 1.0
  }
}
```

---
