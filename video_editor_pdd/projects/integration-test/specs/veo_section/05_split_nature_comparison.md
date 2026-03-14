[split:]

# Section 2.5: Split Nature Comparison

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:13 – 0:14

## Visual Description
A split-screen comparison layout divides the frame vertically into two halves. The left half shows a still from the ocean wave footage (beach/sunset), and the right half shows a still from the aerial forest canopy footage. A thin vertical divider animates from top to bottom at the center. Labels identify each scene. The split reinforces the diversity of Veo-generated footage — two distinct natural environments created by the same AI pipeline.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Black (#000000) visible only as the 4px center divider gap
- No grid lines

### Chart/Visual Elements
- **Left panel (x: 0–958, y: 0–1080):**
  - Content: Ocean wave sunset still frame, scaled to cover and center-cropped
  - Label: "Ocean · Sunset" — positioned bottom-left at (40, 1020)
  - Label background: pill shape, #0B1120 at 70% opacity, padding 8px 16px, border-radius 20px
- **Right panel (x: 962–1920, y: 0–1080):**
  - Content: Forest canopy still frame, scaled to cover and center-cropped
  - Label: "Forest · Canopy" — positioned bottom-right at (1880, 1020), right-aligned
  - Label background: pill shape, #0B1120 at 70% opacity, padding 8px 16px, border-radius 20px
- **Center divider:**
  - 4px wide, white (#FFFFFF) at 90% opacity
  - Position: x: 958, full height

### Animation Sequence
1. **Frame 0–8 (0–0.27s):** Both panels scale in from 1.1→1.0 (subtle zoom-out settle). Panels are clipped to their respective halves
2. **Frame 8–18 (0.27–0.6s):** Center divider draws top-to-bottom (height 0→1080px)
3. **Frame 14–22 (0.47–0.73s):** Left label fades in (opacity 0→1, translateY +10→0)
4. **Frame 18–26 (0.6–0.87s):** Right label fades in (opacity 0→1, translateY +10→0)
5. **Frame 26–30 (0.87–1.0s):** Hold — full split visible

### Typography
- Panel labels: Inter SemiBold, 20px, white (#FFFFFF)

### Easing
- Panel zoom settle: `easeOutQuad`
- Divider draw: `easeInOutCubic`
- Label fade: `easeOutCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <SplitScreen
    leftSrc="/veo/ocean_wave_sunset_still.jpg"
    leftLabel="Ocean · Sunset"
    rightSrc="/veo/aerial_forest_canopy_still.jpg"
    rightLabel="Forest · Canopy"
    dividerColor="#FFFFFF"
    dividerWidth={4}
  />
</Sequence>
```

## Data Points
```json
{
  "left": {
    "label": "Ocean · Sunset",
    "source": "ocean_wave_sunset_still.jpg",
    "scene": "beach at golden hour"
  },
  "right": {
    "label": "Forest · Canopy",
    "source": "aerial_forest_canopy_still.jpg",
    "scene": "aerial forest with dappled light"
  }
}
```

---
