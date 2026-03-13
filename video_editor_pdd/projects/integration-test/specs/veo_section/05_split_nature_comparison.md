[split:] Split Nature Comparison

# Section 2.5: Split Nature Comparison

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:14 – 0:18

## Visual Description
A vertical split-screen comparison showing two Veo-generated nature clips side by side. The left panel reveals an ocean-at-sunset shot while the right panel reveals an aerial forest canopy. A thin blue vertical divider draws top-to-bottom at centre, then both panels wipe outward from the divider. Labels fade in near the bottom of each panel. Both clips apply a subtle Ken Burns zoom throughout.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`

### Chart/Visual Elements
- **Vertical divider:** 3px wide, colour `#5B9BD5`, positioned at X=960px, full height
- **Left panel (0–957px):** Video `veo/ocean_sunset.mp4`, label "Ocean at Sunset" at (480, 980)
- **Right panel (963–1920px):** Video `veo/aerial_forest.mp4`, label "Forest Canopy" at (1440, 980)
- **Inner-edge vignette:** 20px gradient from transparent to `rgba(0,0,0,0.6)` on each panel's inner edge
- **Ken Burns zoom:** Both panels scale 1.0 → 1.05 linearly over full duration

### Animation Sequence
1. **Frame 0–20 (0–0.67s):** Vertical divider draws top-to-bottom (height 0 → 1080px) with `easeInOutCubic`
2. **Frame 15–45 (0.5–1.5s):** Left panel wipes from centre toward left edge via clip-path with `easeOutQuad`
3. **Frame 20–50 (0.67–1.67s):** Right panel wipes from centre toward right edge via clip-path with `easeOutQuad`
4. **Frame 50–70 (1.67–2.33s):** Both labels fade in (opacity 0 → 0.9) with `easeOutCubic`
5. **Frame 0–120 (0–4s):** Ken Burns zoom runs continuously on both video panels (linear)

### Typography
- Labels: Inter, 24px, weight 600, `#FFFFFF`, opacity 0.9

### Easing
- Divider draw: `Easing.inOut(Easing.cubic)`
- Panel wipes: `Easing.out(Easing.quad)`
- Label fade: `Easing.out(Easing.cubic)`
- Ken Burns: linear

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: "#0D1117" }}>
    <VerticalDivider x={960} color="#5B9BD5" drawFrames={[0, 20]} />
    <SplitPanel
      side="left"
      video="veo/ocean_sunset.mp4"
      label="Ocean at Sunset"
      wipeFrames={[15, 45]}
    />
    <SplitPanel
      side="right"
      video="veo/aerial_forest.mp4"
      label="Forest Canopy"
      wipeFrames={[20, 50]}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "divider": {
    "x": 960,
    "width": 3,
    "color": "#5B9BD5"
  },
  "panels": [
    {
      "side": "left",
      "video": "veo/ocean_sunset.mp4",
      "label": "Ocean at Sunset",
      "labelPosition": [480, 980]
    },
    {
      "side": "right",
      "video": "veo/aerial_forest.mp4",
      "label": "Forest Canopy",
      "labelPosition": [1440, 980]
    }
  ],
  "kenBurnsZoom": [1.0, 1.05],
  "vignetteWidth": 20,
  "vignetteOpacity": 0.6
}
```

---
