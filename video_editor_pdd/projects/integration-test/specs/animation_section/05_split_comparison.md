[split:]

# Section 1.5: Circle vs Square Split Comparison

**Tool:** Remotion
**Duration:** ~1.1s (33 frames @ 30fps)
**Timestamp:** 0:05 – 0:06

## Visual Description
A split-screen layout divides the canvas vertically into two equal panels. The left panel (blue-tinted background) showcases a blue circle; the right panel (green-tinted background) showcases a green square. A thin white vertical divider draws downward to separate the panels. Each shape scales in with spring animation, slightly staggered. Labels "Circle" and "Square" fade in beneath each shape. Both shapes gently breathe in a synchronized loop.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Split — Left: #0F172A (blue-navy tint), Right: #0F2318 (green-navy tint)
- No grid lines

### Chart/Visual Elements
- **Vertical divider:** 2px wide, #FFFFFF at 25% opacity, centered at x=640, full height (720px)
- **Left panel — Blue circle:** 120px diameter, #3B82F6, centered in left half (x=320, y=320)
- **Right panel — Green square:** 110x110px, #22C55E, border-radius 6px, centered in right half (x=960, y=320)
- **Left label:** "Circle" — positioned at (320, 420), centered
- **Right label:** "Square" — positioned at (960, 420), centered
- **Panel backgrounds:** Soft gradient overlays from each panel's tint color

### Animation Sequence
1. **Frame 0–8 (0–0.27s):** Vertical divider draws in from center outward (height 0→720px, expanding from y=360 up and down simultaneously). Panel backgrounds tint in from base #141921 to their respective colors.
2. **Frame 8–15 (0.27–0.5s):** Blue circle scales in from 0→1.0x with spring overshoot (starts frame 8). Green square scales in from 0→1.0x with spring overshoot (starts frame 10, 2-frame stagger).
3. **Frame 15–20 (0.5–0.67s):** Labels fade in — "Circle" at frame 15, "Square" at frame 17. Both use opacity 0→1 with translateY +10px→0px.
4. **Frame 20–33 (0.67–1.1s):** Breathing loop — both shapes oscillate scale between 1.0x and 1.04x on a synchronized 15-frame sinusoidal cycle (in phase).

### Typography
- Labels: Inter, 24px, #FFFFFF at 80% opacity, font-weight 500, text-align center
- No title text

### Easing
- Divider draw: `easeInOutCubic`
- Shape scale-in: `spring({ damping: 12, stiffness: 180, mass: 1 })`
- Label fade: `easeOutQuad`
- Breathing: `sinusoidal` (continuous, 15-frame period)
- Panel tint: `easeOutQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={33}>
  <AbsoluteFill>
    {/* Left panel */}
    <div style={{ position: "absolute", left: 0, width: "50%", height: "100%", backgroundColor: leftBg }}>
      <BreathingShape shape="circle" diameter={120} color="#3B82F6" scale={circleScale} />
      <Sequence from={15}>
        <FadeLabel text="Circle" />
      </Sequence>
    </div>
    {/* Right panel */}
    <div style={{ position: "absolute", right: 0, width: "50%", height: "100%", backgroundColor: rightBg }}>
      <Sequence from={2}>
        <BreathingShape shape="square" size={110} color="#22C55E" scale={squareScale} borderRadius={6} />
      </Sequence>
      <Sequence from={17}>
        <FadeLabel text="Square" />
      </Sequence>
    </div>
    {/* Divider */}
    <VerticalDivider height={dividerHeight} color="rgba(255,255,255,0.25)" />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "layout": "split-vertical",
  "divider": {
    "width": 2,
    "color": "rgba(255,255,255,0.25)"
  },
  "left": {
    "background": "#0F172A",
    "shape": "circle",
    "diameter": 120,
    "color": "#3B82F6",
    "label": "Circle",
    "scaleInFrame": 8
  },
  "right": {
    "background": "#0F2318",
    "shape": "square",
    "size": 110,
    "color": "#22C55E",
    "borderRadius": 6,
    "label": "Square",
    "scaleInFrame": 10
  },
  "breathing": {
    "minScale": 1.0,
    "maxScale": 1.04,
    "period": 15
  }
}
```

---

<!-- ANNOTATION_UPDATE_START: test-batch-ann-1773422512345 -->
## Annotation Update
Requested change: Change the primary background accent in Animation Section to #00FF00.
Technical assessment: The current color treatment should shift to a clearly visible green accent.
- Update the background accent color to #00FF00
<!-- ANNOTATION_UPDATE_END: test-batch-ann-1773422512345 -->
