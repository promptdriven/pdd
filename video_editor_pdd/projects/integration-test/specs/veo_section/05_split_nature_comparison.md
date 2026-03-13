[split:]

# Section 2.5: Split Nature Comparison

**Tool:** Remotion
**Duration:** ~0.03s (1 frame transition beat)
**Timestamp:** 0:05 - 0:05

## Visual Description
A split-screen comparison placing the ocean sunset footage side-by-side with the aerial forest footage. The screen divides vertically at the center with a glowing separator line. The left panel shows a still from the ocean B-roll with the label "OCEAN — Sunset" below. The right panel shows a still from the forest cutaway with "FOREST — Canopy" below. A header reads "VEO GENERATION RANGE". This beat is a brief transitional flash — it appears for approximately 1 frame as a visual punctuation mark between the data overlay and the infographic.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0D1B2A
- No grid lines

### Chart/Visual Elements
- **Left panel:** 940x810 at position (10, 140), contains ocean still frame, rounded corners 8px
- **Right panel:** 940x810 at position (970, 140), contains forest still frame, rounded corners 8px
- **Center divider:** Vertical line at x=960, height 810px, 2px solid #4DA8DA, box-shadow glow 0 0 12px #4DA8DA
- **Left label:** "OCEAN — Sunset" centered below left panel at y=980, color #FFD4A8
- **Right label:** "FOREST — Canopy" centered below right panel at y=980, color #A8E6CF
- **Header:** "VEO GENERATION RANGE" centered at y=60

### Animation Sequence
1. **Frame 0-1 (0-0.03s):** All elements appear instantly (single-frame beat). No animated transitions — this is a flash card.

### Typography
- Header: Inter Bold, 32px, #FFFFFF, letter-spacing 8px
- Panel labels: Inter SemiBold, 20px, respective colors (#FFD4A8 / #A8E6CF)

### Easing
- None (single-frame display)

## Narration Sync
> (Transitional beat — no dedicated narration)

## Code Structure (Remotion)
```typescript
<Sequence from={153} durationInFrames={1}>
  <AbsoluteFill style={{ backgroundColor: '#0D1B2A' }}>
    <HeaderText text="VEO GENERATION RANGE" />
    <SplitPanel
      left={<StillFrame src={staticFile("veo/04_veo_broll.mp4")} frame={15} />}
      right={<StillFrame src={staticFile("veo/05_veo_cutaway.mp4")} frame={15} />}
      dividerColor="#4DA8DA"
    />
    <PanelLabel side="left" text="OCEAN — Sunset" color="#FFD4A8" />
    <PanelLabel side="right" text="FOREST — Canopy" color="#A8E6CF" />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "header": "VEO GENERATION RANGE",
  "panels": [
    { "side": "left", "label": "OCEAN — Sunset", "source": "veo/04_veo_broll.mp4", "color": "#FFD4A8" },
    { "side": "right", "label": "FOREST — Canopy", "source": "veo/05_veo_cutaway.mp4", "color": "#A8E6CF" }
  ]
}
```
