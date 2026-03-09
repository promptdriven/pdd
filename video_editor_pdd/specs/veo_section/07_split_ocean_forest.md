[split:]

# Section 2.7: Split Screen — Ocean & Forest

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:18 - 0:21

## Visual Description
A split-screen comparison showing the ocean wave sunset footage on the left and the forest canopy aerial footage on the right. A thin vertical divider separates the two panels. Each side has a small label at the bottom identifying the scene. The split line animates in from center, pushing the two panels apart, creating a dramatic reveal.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Black (#000000) visible only as the center divider gap

### Chart/Visual Elements
- Left panel: Ocean wave sunset clip, cropped to 948x1080, positioned at X=0
- Right panel: Forest canopy aerial clip, cropped to 948x1080, positioned at X=972
- Vertical divider: 4px wide, #FFFFFF at 80% opacity, centered at X=960
- Divider glow: 24px wide soft glow behind divider, #F59E0B at 20% opacity
- Left label: "OCEAN — SUNSET" in bottom-left of left panel (X=40, Y=1020)
- Right label: "FOREST — AERIAL" in bottom-right of right panel (X=1680, Y=1020)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Both panels start at full-width (each 1920px), centered and overlapping. They slide apart to reveal the split: left panel slides to X=0, right panel slides to X=972. Divider fades in.
2. **Frame 20-30 (0.67-1s):** Labels fade in from 0% to 100% opacity with upward drift.
3. **Frame 30-75 (1-2.5s):** Hold — both panels play their respective clips side by side.
4. **Frame 75-90 (2.5-3s):** Labels fade out. Panels hold.

### Typography
- Panel labels: Inter SemiBold, 16px, #FFFFFF at 90% opacity, letter-spacing 2px, uppercase
- No additional text

### Easing
- Panel slide: `easeOutCubic`
- Divider fade: `easeOutQuad`
- Label fade: `easeOutQuad`

## Narration Sync
> (No narration — visual comparison beat between narration segments)

## Code Structure (Remotion)
```typescript
<Sequence from={540} durationInFrames={90}>
  <SplitScreen
    leftSrc={staticFile("veo/ocean_wave_sunset.mp4")}
    rightSrc={staticFile("veo/forest_canopy_aerial.mp4")}
    dividerColor="#FFFFFF"
    dividerGlow="#F59E0B"
  />
  <Sequence from={20}>
    <SplitLabels left="OCEAN — SUNSET" right="FOREST — AERIAL" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "leftClip": "veo/ocean_wave_sunset.mp4",
  "rightClip": "veo/forest_canopy_aerial.mp4",
  "leftLabel": "OCEAN — SUNSET",
  "rightLabel": "FOREST — AERIAL",
  "dividerColor": "#FFFFFF"
}
```

---
