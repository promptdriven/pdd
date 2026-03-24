[split:]

# Section 1.5: Split Comparison

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:04 - 0:05

## Visual Description
A split-screen comparison layout slides up from below the viewport. The left panel shows a blue circle labeled "Before" on a dark blue background; the right panel shows an indigo rounded square labeled "After" on a dark indigo background. A thin white vertical divider separates the two halves. Both shapes gently float (bob up and down) once the panels settle into place, creating a calm, living feel.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Outer background `#0A1628`
- Grid lines: None

### Chart/Visual Elements
- **Left Panel:** Background `#1E3A5F`, width 960px
  - Circle: radius 50px, fill `#3B82F6`, centered at (480, 540)
  - Label: "Before" at Y=420px
- **Right Panel:** Background `#312E81`, width 960px
  - Rounded Square: 100px, border-radius 12px, fill `#6366F1`, centered at (480, 540) within right panel
  - Label: "After" at Y=420px
- **Vertical Divider:** 2px wide, white `#FFFFFF` at 60% opacity, centered at X=960
- **Float Animation:** Both shapes bob ±5px vertically with a 20-frame period

### Animation Sequence
1. **Frame 0-12 (0-0.4s):** Both panels slide up from Y=1080 to Y=0 (the entire split layout enters from bottom)
2. **Frame 8-18 (0.27-0.6s):** "Before" label fades in (opacity 0→0.9) on left panel
3. **Frame 12-22 (0.4-0.73s):** "After" label fades in (opacity 0→0.9) on right panel
4. **Frame 15-30 (0.5-1.0s):** Both shapes begin gentle floating bob (±5px, 20-frame period)

### Typography
- Labels: Inter, 24px, semi-bold (600), white `#FFFFFF`, opacity 0.9

### Easing
- Slide up: `easeOut(cubic)`
- Label fade: `easeOut(quad)`
- Float bob: `sin` (sinusoidal oscillation)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  {/* Left Panel */}
  <AnimatedCircle
    center={[480, 540]}
    radius={50}
    color="#3B82F6"
    floatAmplitude={5}
    floatPeriod={20}
  />
  <FadeInLabel text="Before" y={420} startFrame={8} />

  {/* Divider */}
  <VerticalDivider x={960} width={2} opacity={0.6} />

  {/* Right Panel */}
  <AnimatedSquare
    center={[480, 540]}
    size={100}
    borderRadius={12}
    color="#6366F1"
    floatAmplitude={5}
    floatPeriod={20}
  />
  <FadeInLabel text="After" y={420} startFrame={12} />
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "background": "#1E3A5F",
    "shape": "circle",
    "shapeColor": "#3B82F6",
    "radius": 50,
    "label": "Before"
  },
  "rightPanel": {
    "background": "#312E81",
    "shape": "roundedSquare",
    "shapeColor": "#6366F1",
    "size": 100,
    "borderRadius": 12,
    "label": "After"
  },
  "divider": {
    "color": "#FFFFFF",
    "opacity": 0.6,
    "width": 2
  },
  "float": {
    "amplitude": 5,
    "period": 20
  }
}
```

---
