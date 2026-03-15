[Remotion]

# Section 1.8: Key Visual — Bar Chart

**Tool:** Remotion
**Duration:** ~0.8s (24 frames @ 30fps)
**Timestamp:** 0:06 - 0:07

## Visual Description
An animated vertical bar chart with four bars grows upward from the baseline in a staggered sequence. The bars alternate between cyan and green colors, each reaching a different height. The bars grow with a satisfying overshoot (back easing), giving them a springy, organic feel. A subtle pulse highlights the tallest bar after all bars have finished growing. Faint grid lines provide reference in the background.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark blue `#0A1628` (solid fill)
- Grid lines: Horizontal, `rgba(255, 255, 255, 0.05)`, evenly spaced

### Chart/Visual Elements
- **Bar A:** Width 120px, target height 300px, fill `#38BDF8` (cyan), label "A"
- **Bar B:** Width 120px, target height 420px, fill `#22C55E` (green), label "B"
- **Bar C:** Width 120px, target height 260px, fill `#38BDF8` (cyan), label "C"
- **Bar D:** Width 120px, target height 500px, fill `#22C55E` (green), label "D"
- **Bar Gap:** 30px between bars
- **Max Height:** 500px
- **Container Width:** 600px, bottom at Y=880px
- **Bar Border Radius:** 8px 8px 0 0 (rounded top corners only)
- **Bar Shadow:** `rgba(0, 0, 0, 0.3)` drop shadow

### Animation Sequence
1. **Frame 0-4 (0-0.13s):** Chart label fades in (opacity 0→0.7) at position (80, 60)
2. **Frame 0-8 (0-0.27s):** Bar A grows from height 0→300px
3. **Frame 3-11 (0.1-0.37s):** Bar B grows from height 0→420px (3-frame stagger)
4. **Frame 6-14 (0.2-0.47s):** Bar C grows from height 0→260px (3-frame stagger)
5. **Frame 9-17 (0.3-0.57s):** Bar D grows from height 0→500px (3-frame stagger)
6. **Frame 19-24 (0.63-0.8s):** Pulse highlight on tallest bar (Bar D) — brief opacity/glow pulse

### Typography
- Labels: Inter, 20px, semi-bold (600), white `#FFFFFF`, opacity 0.7
- Label position: (80, 60) — top-left corner

### Easing
- Bar grow: `easeOut(back(1.4))` — overshoot with 1.4 factor
- Label fade: `easeOut(quad)`
- Pulse: `linear` fade

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={24}>
  <GridLines spacing={100} color="rgba(255,255,255,0.05)" />
  {bars.map((bar, i) => (
    <Sequence key={bar.label} from={i * 3}>
      <AnimatedBar
        width={120}
        targetHeight={bar.height}
        color={bar.color}
        label={bar.label}
        growDuration={8}
      />
    </Sequence>
  ))}
</Sequence>
```

## Data Points
```json
{
  "bars": [
    { "label": "A", "height": 300, "color": "#38BDF8" },
    { "label": "B", "height": 420, "color": "#22C55E" },
    { "label": "C", "height": 260, "color": "#38BDF8" },
    { "label": "D", "height": 500, "color": "#22C55E" }
  ],
  "barWidth": 120,
  "barGap": 30,
  "maxHeight": 500,
  "containerWidth": 600,
  "containerBottomY": 880,
  "barBorderRadius": "8px 8px 0 0",
  "staggerFrames": 3,
  "growDuration": 8,
  "backgroundColor": "#0A1628"
}
```

---
