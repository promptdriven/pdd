[split:]

# Section 1.9: Split Summary

**Tool:** Remotion
**Duration:** ~0.73s (22 frames @ 30fps)
**Timestamp:** 0:07 - 0:08

## Visual Description
A final split-screen summary card fades into view, divided by a glowing cyan vertical line that slowly drifts from left to right. The left half has a slightly lighter dark background; the right half is near-black. The animated divider emits a soft cyan glow as it traverses. A small "Split Summary" label fades in at the top-left corner to close out the section.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Near-black `#020617`
- Grid lines: None

### Chart/Visual Elements
- **Left Panel:** Background `#0F172A` at 90% opacity
- **Right Panel:** Background `#020617` at 100% opacity
- **Divider Line:** 3px wide, `#38BDF8` (cyan)
  - Start X: 640px
  - End X: 720px (drifts rightward)
  - Glow: `#38BDF8`, blur 24px, width 20px, opacity 0.3
- **Label:** "Split Summary" at position (80, 60)

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Entire card fades in (opacity 0→1)
2. **Frame 6-18 (0.2-0.6s):** Divider line drifts from X=640 to X=720, with cyan glow trailing
3. **Frame 18-22 (0.6-0.73s):** "Split Summary" label fades in (opacity 0→0.7)

### Typography
- Label: Inter, 20px, semi-bold (600), white `#FFFFFF`, opacity 0.7

### Easing
- Card fade in: `easeOut(quad)`
- Divider drift: `easeInOut(sin)`
- Label fade: `easeOut(quad)`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={22}>
  <SplitBackground
    leftColor="#0F172A"
    rightColor="#020617"
  />
  <Sequence from={6}>
    <DividerLine
      startX={640}
      endX={720}
      color="#38BDF8"
      width={3}
      glowBlur={24}
      glowOpacity={0.3}
    />
  </Sequence>
  <Sequence from={18}>
    <SplitLabel text="Split Summary" x={80} y={60} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "leftBackground": "#0F172A",
  "leftOpacity": 0.9,
  "rightBackground": "#020617",
  "rightOpacity": 1.0,
  "divider": {
    "startX": 640,
    "endX": 720,
    "color": "#38BDF8",
    "width": 3,
    "glowBlur": 24,
    "glowOpacity": 0.3,
    "glowWidth": 20
  },
  "label": {
    "text": "Split Summary",
    "x": 80,
    "y": 60,
    "fontSize": 20,
    "fontWeight": 600,
    "color": "#FFFFFF",
    "opacity": 0.7
  }
}
```

---
