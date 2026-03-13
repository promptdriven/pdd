[Remotion]

# Section 1.4: Green Square Slide Right

**Tool:** Remotion
**Duration:** ~1.1s (33 frames @ 30fps)
**Timestamp:** 0:04 – 0:05

## Visual Description
The green square from the previous morph slides horizontally from the center of the canvas to the right side, leaving behind a motion trail of fading ghost copies. A horizontal guide line fades in briefly to emphasize the linear motion path. The square overshoots its target position slightly before settling. The motion trail consists of 4 progressively fainter copies trailing behind the leading shape.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Dark charcoal (#141921)
- No grid lines

### Chart/Visual Elements
- **Green square:** 160x160px, #22C55E, border-radius 8px
- **Starting position:** Canvas center (x=640)
- **Target position:** Right offset (x=920)
- **Overshoot position:** x=935 (15px past target)
- **Guide line:** Horizontal, y=360, 1px height, #FFFFFF at 15% opacity, full canvas width
- **Motion trail:** 4 ghost copies trailing behind:
  - Trail 1: 40px behind, 3-frame delay, opacity 0.15
  - Trail 2: 80px behind, 6-frame delay, opacity 0.10
  - Trail 3: 120px behind, 9-frame delay, opacity 0.06
  - Trail 4: 160px behind, 12-frame delay, opacity 0.03

### Animation Sequence
1. **Frame 0–3 (0–0.1s):** Hold square at center (x=640). Guide line fades in from 0→0.15 opacity.
2. **Frame 3–22 (0.1–0.73s):** Square slides from x=640 to x=935 (overshoot). Motion trail activates — each ghost follows with staggered delay. Trail ghosts use the same square shape at reduced opacity.
3. **Frame 22–27 (0.73–0.9s):** Overshoot settle — square springs back from x=935 to x=920. Trail ghosts converge and fade out.
4. **Frame 27–33 (0.9–1.1s):** Guide line fades out to 0 opacity. Subtle green glow appears behind square at rest position (rgba(34, 197, 94, 0.2), 30px blur).

### Typography
- None

### Easing
- Slide motion: `easeOutCubic` (with overshoot)
- Overshoot settle: `spring({ damping: 16, stiffness: 220, mass: 1 })`
- Guide line fade: `easeInOutQuad`
- Trail fade: `linear` per ghost

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={33}>
  <AbsoluteFill style={{ backgroundColor: "#141921" }}>
    <GuideLine
      y={360}
      opacity={guideOpacity}
      color="rgba(255,255,255,0.15)"
    />
    {trails.map((trail, i) => (
      <TrailGhost
        key={i}
        x={trail.x}
        opacity={trail.opacity}
        size={160}
        color="#22C55E"
        borderRadius={8}
      />
    ))}
    <SlidingSquare
      x={squareX}
      size={160}
      color="#22C55E"
      borderRadius={8}
      glowOpacity={restGlowOpacity}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "square": {
    "size": 160,
    "color": "#22C55E",
    "borderRadius": 8
  },
  "motion": {
    "startX": 640,
    "targetX": 920,
    "overshootX": 935
  },
  "trails": [
    { "offset": 40, "delay": 3, "opacity": 0.15 },
    { "offset": 80, "delay": 6, "opacity": 0.10 },
    { "offset": 120, "delay": 9, "opacity": 0.06 },
    { "offset": 160, "delay": 12, "opacity": 0.03 }
  ]
}
```

---
