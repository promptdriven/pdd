[split:]

# Section 1.5: Split Comparison

**Tool:** Remotion
**Duration:** ~1.0s (30 frames @ 30fps)
**Timestamp:** 0:06 - 0:07

## Visual Description
A split-screen comparison slides up from below the viewport. The left panel (dark blue) contains a blue circle representing "Before", and the right panel (dark indigo) contains an indigo rounded square representing "After". A thin white vertical divider separates the two panels. Labels "Before" and "After" fade in beneath their respective shapes with a staggered timing.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep navy (#0A1628) — visible momentarily before the split layout slides up

### Chart/Visual Elements
- **Left panel:** 960x1080px, background #1E3A5F (dark blue)
  - Blue circle: centered at (480, 440) within panel, radius 80px, fill #3B82F6
  - "Before" label: centered at (480, 580) within panel
- **Right panel:** 960x1080px, background #312E81 (dark indigo)
  - Indigo square: centered at (480, 440) within panel, 120x120px, border-radius 12px, fill #6366F1
  - "After" label: centered at (480, 580) within panel
- **Vertical divider:** 2px wide, white (#FFFFFF), full height, centered at x=960, max opacity 0.6

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Slide up — entire split layout translates from y=1080 to y=0 (enters from bottom)
2. **Frame 12-22 (0.4-0.73s):** "Before" label fades in (opacity 0 → 1)
3. **Frame 15-25 (0.5-0.83s):** "After" label fades in (opacity 0 → 1)
4. **Frame 25-30 (0.83-1.0s):** Hold — all elements visible

### Typography
- Labels: Inter 600, 24px, white (#FFFFFF), opacity 0.9

### Easing
- Slide up: `easeOutCubic`
- Label fade-in: `linear`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
  <div style={{ transform: `translateY(${slideY}px)` }}>
    {/* Left panel: circle */}
    <div style={{ width: 960, height: 1080, backgroundColor: '#1E3A5F' }}>
      <AnimatedCircle />
    </div>
    {/* Right panel: square */}
    <div style={{ width: 960, height: 1080, backgroundColor: '#312E81' }}>
      <AnimatedSquare />
    </div>
    <VerticalDivider />
    <FadeInLabel text="Before" panelLeft={0} />
    <FadeInLabel text="After" panelLeft={960} />
  </div>
</AbsoluteFill>
```

## Data Points
```json
{
  "layout": {
    "panelWidth": 960,
    "dividerWidth": 2,
    "dividerMaxOpacity": 0.6
  },
  "shapes": {
    "circle": { "x": 480, "y": 440, "radius": 80, "color": "#3B82F6" },
    "square": { "x": 480, "y": 440, "size": 120, "borderRadius": 12, "color": "#6366F1" }
  }
}
```

---
