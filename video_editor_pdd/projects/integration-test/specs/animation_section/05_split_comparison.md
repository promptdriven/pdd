[split:]

# Section 1.5: Circle vs Square Split Comparison

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:13 - 0:16

## Visual Description
A split-screen layout showing the blue circle on the left panel and the green square on the right panel, separated by a vertical divider line. Each shape sits centered within its half and gently loops a breathing animation. Labels beneath each shape identify them. This serves as a visual recap of the transformation that just occurred.

## Technical Specifications

### Canvas
- Resolution: 1280x720 (16:9)
- Background: Left panel #0F172A, Right panel #0F2318
- Divider: Vertical line at x=640, 2px wide, white (#FFFFFF) at 25% opacity

### Chart/Visual Elements
- Left panel (x: 0-640): Blue circle (#3B82F6), 120px diameter, centered at (320, 320)
- Right panel (x: 640-1280): Green square (#22C55E), 110px, centered at (960, 320)
- Label "Circle": positioned at (320, 440), white text
- Label "Square": positioned at (960, 440), white text
- Divider: Vertical line, full height, center of canvas

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider line draws from center outward (y=360 expanding up and down simultaneously). Left panel tints in. Right panel tints in.
2. **Frame 20-40 (0.67-1.33s):** Blue circle scales in on left side (0 → 1.0). Green square scales in on right side (0 → 1.0). Both staggered by 5 frames.
3. **Frame 40-55 (1.33-1.83s):** Labels fade in beneath each shape.
4. **Frame 55-90 (1.83-3.0s):** Both shapes loop a gentle breathing animation (scale 1.0 → 1.04 → 1.0, 30-frame cycle). Elements hold.

### Typography
- Labels: Inter Medium, 24px, white (#FFFFFF) at 70% opacity

### Easing
- Divider draw: `easeOutCubic`
- Shape scale-in: `spring({ damping: 12, stiffness: 180 })`
- Label fade: `easeOutQuad`
- Breathing loop: `easeInOutSine`

## Narration Sync
> (No narration — visual recap between narration segments)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  <AbsoluteFill style={{ display: 'flex', flexDirection: 'row' }}>
    <SplitPanel bgColor="#0F172A" flex={1}>
      <Sequence from={20}>
        <AnimatedCircle diameter={120} color="#3B82F6" />
      </Sequence>
      <Sequence from={40}>
        <FadeInLabel text="Circle" />
      </Sequence>
    </SplitPanel>
    <VerticalDivider drawStart={0} drawEnd={20} />
    <SplitPanel bgColor="#0F2318" flex={1}>
      <Sequence from={25}>
        <AnimatedSquare size={110} color="#22C55E" />
      </Sequence>
      <Sequence from={40}>
        <FadeInLabel text="Square" />
      </Sequence>
    </SplitPanel>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "layout": "split",
  "panels": [
    {
      "side": "left",
      "shape": "circle",
      "color": "#3B82F6",
      "size": 120,
      "label": "Circle",
      "bgColor": "#0F172A"
    },
    {
      "side": "right",
      "shape": "square",
      "color": "#22C55E",
      "size": 110,
      "label": "Square",
      "bgColor": "#0F2318"
    }
  ]
}
```

---
