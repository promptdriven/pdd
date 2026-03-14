[Remotion]

# Section 1.4: Square Slide Right

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:05 - 0:06

## Visual Description
The indigo rounded square from the morph animation slides dynamically from the center of the screen to the right. The motion follows a physically-inspired sequence: a brief anticipation pull to the left, a fast main slide to the right, a slight overshoot past the target, and a soft bounce back to rest. A horizontal motion streak trails behind the square during movement, reinforcing the sense of speed.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Radial gradient — dark slate (#1E293B) at center to dark navy (#0F172A) at edges

### Chart/Visual Elements
- **Sliding square:** 120x120px, border-radius 12px, fill #6366F1 (indigo), vertically centered at y=540
  - Start position: x=960 (center)
  - Target position: x=1440 (right third)
  - Anticipation offset: -10px (shifts left briefly)
  - Overshoot: +20px past target
- **Motion streak:** Horizontal trail behind square, color rgba(99, 102, 241, 0.3), max length 200px, fades as square decelerates

### Animation Sequence
1. **Frame 0-3 (0-0.1s):** Anticipation — square shifts 10px to the left (x 960 → 950)
2. **Frame 3-21 (0.1-0.7s):** Main slide — square accelerates right from x=950 to x=1460 (overshooting target by 20px), motion streak visible
3. **Frame 21-27 (0.7-0.9s):** Bounce back — square eases back from x=1460 to x=1440, streak fades
4. **Frame 27-30 (0.9-1.0s):** Settle — square holds at x=1440

### Typography
- None

### Easing
- Anticipation: `easeInQuad`
- Main slide: `easeOutCubic`
- Bounce: `easeInOutSine`
- Motion streak opacity: `easeOut`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{
  background: 'radial-gradient(circle at center, #1E293B 0%, #0F172A 100%)'
}}>
  <MotionStreak />
  <SlidingSquare />
</AbsoluteFill>
```

## Data Points
```json
{
  "slide": {
    "fromX": 960,
    "toX": 1440,
    "y": 540,
    "anticipationOffset": -10,
    "overshoot": 20,
    "streakMaxLength": 200
  },
  "square": {
    "size": 120,
    "borderRadius": 12,
    "color": "#6366F1"
  }
}
```

---

<!-- ANNOTATION_UPDATE_START: test-batch-ann-1773531287657 -->
## Annotation Update
Requested change: Change the primary background accent in Animation Section to #00FF00.
Technical assessment: The current color treatment should shift to a clearly visible green accent.
- Update the background accent color to #00FF00
<!-- ANNOTATION_UPDATE_END: test-batch-ann-1773531287657 -->

<!-- ANNOTATION_UPDATE_START: test-batch-ann-1773531454328 -->
## Annotation Update
Requested change: Change the primary background accent in Animation Section to #00FF00.
Technical assessment: The current color treatment should shift to a clearly visible green accent.
- Update the background accent color to #00FF00
<!-- ANNOTATION_UPDATE_END: test-batch-ann-1773531454328 -->
