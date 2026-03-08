[split:]

# Section 2.8: Split Summary — Ocean & Forest

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:08 - 0:11

## Visual Description
A split-screen layout showcasing both Veo-generated clips side by side as a visual recap. The left panel shows a still frame from the ocean sunset clip, and the right panel shows a still frame from the forest canopy clip. A vertical divider wipes in from top to bottom, separating the two scenes. Each side has a descriptive label beneath the imagery. A centered badge at the intersection reads "Veo 3.1" to highlight the generation technology.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Deep charcoal (#0F1419)
- Grid lines: none

### Chart/Visual Elements
- Left panel: left half of screen (0-955px)
  - Ocean sunset still: cropped to fill left half, slight Ken Burns zoom (scale 1.0→1.05)
  - Warm color tint overlay: #F59E0B08
  - Label "Ocean at Sunset": centered at (478, 960), color #D4A574
- Right panel: right half of screen (965-1920px)
  - Forest canopy still: cropped to fill right half, slight Ken Burns zoom (scale 1.0→1.05)
  - Cool color tint overlay: #22C55E08
  - Label "Forest Canopy": centered at (1442, 960), color #86EFAC
- Vertical divider: at x=960, 3px wide, color #475569, height animates from 0→1080
- Center badge: pill shape at (960, 500), 140x44px, background #1E293BCC, border 1px #D4A57460, borderRadius 22px
  - Badge text: "Veo 3.1" — color #F8FAFC, 16px

### Animation Sequence
1. **Frame 0-18 (0-0.6s):** Vertical divider wipes down from top (height 0→1080). Both panels begin Ken Burns zoom.
2. **Frame 10-30 (0.33-1.0s):** Left panel (ocean) fades in (opacity 0→1). Warm tint overlay appears. "Ocean at Sunset" label fades in with upward translate.
3. **Frame 20-40 (0.67-1.33s):** Right panel (forest) fades in (opacity 0→1). Cool tint overlay appears. "Forest Canopy" label fades in with upward translate.
4. **Frame 35-48 (1.17-1.6s):** Center "Veo 3.1" badge pops in with scale spring (0→1.1→1.0).
5. **Frame 48-90 (1.6-3.0s):** Hold. Ken Burns zoom continues slowly on both panels.

### Typography
- Labels: Inter Medium, 22px
  - Left label: warm gold (#D4A574)
  - Right label: soft green (#86EFAC)
- Center badge: Inter SemiBold, 16px, off-white (#F8FAFC)

### Easing
- Divider wipe: `easeInOutQuad`
- Panel fade/reveal: `easeOutCubic`
- Label translate: `easeOutQuad` (translateY 15px → 0px)
- Badge pop: `spring({ damping: 10, stiffness: 200 })`
- Ken Burns zoom: `linear`

## Narration Sync
> (No narration — visual summary beat as section concludes)

## Code Structure (Remotion)
```typescript
<Sequence from={240} durationInFrames={90}>
  <AbsoluteFill style={{ backgroundColor: "#0F1419" }}>
    <DividerWipe x={960} width={3} duration={18} color="#475569" />
    <Sequence from={10}>
      <SplitPanel side="left">
        <KenBurns scale={[1.0, 1.05]} duration={80}>
          <Img src={staticFile("veo_section/ocean_still.jpg")} />
        </KenBurns>
        <FadeIn duration={20}>
          <Label text="Ocean at Sunset" color="#D4A574" y={960} />
        </FadeIn>
      </SplitPanel>
    </Sequence>
    <Sequence from={20}>
      <SplitPanel side="right">
        <KenBurns scale={[1.0, 1.05]} duration={70}>
          <Img src={staticFile("veo_section/forest_still.jpg")} />
        </KenBurns>
        <FadeIn duration={20}>
          <Label text="Forest Canopy" color="#86EFAC" y={960} />
        </FadeIn>
      </SplitPanel>
    </Sequence>
    <Sequence from={35}>
      <PopIn spring={{ damping: 10, stiffness: 200 }}>
        <Badge text="Veo 3.1" bgColor="#1E293BCC" borderColor="#D4A57460" />
      </PopIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "leftPanel": {
    "source": "veo_section/ocean_still.jpg",
    "label": "Ocean at Sunset",
    "labelColor": "#D4A574",
    "tintColor": "#F59E0B08"
  },
  "rightPanel": {
    "source": "veo_section/forest_still.jpg",
    "label": "Forest Canopy",
    "labelColor": "#86EFAC",
    "tintColor": "#22C55E08"
  },
  "dividerColor": "#475569",
  "badgeText": "Veo 3.1",
  "kenBurnsScale": [1.0, 1.05]
}
```

---
