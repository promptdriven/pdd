[split:]

# Section 2.5: Split Nature Comparison

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:17 - 0:21

## Visual Description
A split-screen comparison layout showing the two Veo-generated environments side by side. The left panel displays a still frame from the ocean sunset footage; the right panel displays a still frame from the aerial forest footage. A thin vertical divider separates them. Labels appear below each panel identifying the scene. The divider animates in from the top, then both panels reveal simultaneously with a horizontal wipe.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0D1117
- Divider: 3px wide, color #5B9BD5, centered at x=960

### Chart/Visual Elements
- **Left panel (x=0–957):** Still frame from ocean sunset clip, scaled to fill panel with slight ken-burns zoom (1.0→1.05)
- **Right panel (x=963–1920):** Still frame from aerial forest clip, scaled to fill panel with slight ken-burns zoom (1.0→1.05)
- **Divider line:** Vertical, x=960, full height, 3px, color #5B9BD5
- **Left label:** "Ocean at Sunset" — positioned at (480, 980), centered
- **Right label:** "Forest Canopy" — positioned at (1440, 980), centered
- **Subtle vignette:** on each panel edge, 20px soft black gradient inward

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Divider line draws from top to bottom (y=0→1080)
2. **Frame 15-45 (0.5-1.5s):** Left panel wipes in from center-outward (clipPath reveal)
3. **Frame 20-50 (0.67-1.67s):** Right panel wipes in from center-outward (clipPath reveal)
4. **Frame 50-70 (1.67-2.33s):** Labels fade in below each panel
5. **Frame 0-120 (0-4s):** Ken-burns slow zoom runs continuously on both panels

### Typography
- Panel labels: Inter SemiBold, 24px, #FFFFFF, 90% opacity
- No title text

### Easing
- Divider draw: `easeInOutCubic`
- Panel wipe: `easeOutQuad`
- Label fade: `easeOutCubic`
- Ken-burns zoom: `linear`

## Narration Sync
> (No narration — visual recap bridge after second narration beat)

## Code Structure (Remotion)
```typescript
<Sequence from={510} durationInFrames={120}>
  <Background color="#0D1117" />
  <Sequence from={0}>
    <VerticalDivider x={960} color="#5B9BD5" />
  </Sequence>
  <Sequence from={15}>
    <SplitPanel side="left" src={stillFrame("ocean_sunset")} zoom={[1.0, 1.05]}>
      <Label text="Ocean at Sunset" />
    </SplitPanel>
  </Sequence>
  <Sequence from={20}>
    <SplitPanel side="right" src={stillFrame("aerial_forest")} zoom={[1.0, 1.05]}>
      <Label text="Forest Canopy" />
    </SplitPanel>
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "panels": [
    { "side": "left", "source": "ocean_sunset", "label": "Ocean at Sunset" },
    { "side": "right", "source": "aerial_forest", "label": "Forest Canopy" }
  ],
  "divider_color": "#5B9BD5"
}
```

---
