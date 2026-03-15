[split:]

# Section 2.4: Split Nature Comparison

**Tool:** Remotion
**Duration:** ~1.5s
**Timestamp:** 0:12 – 0:13.5

## Visual Description
A split-screen comparison layout showing both Veo-generated clips side by side. The left panel displays the ocean sunset footage labeled "Ocean · Sunset," while the right panel shows the aerial forest canopy footage labeled "Forest · Canopy." A vertical divider line separates the two panels. The panels slide in from their respective edges and meet at center, then labels fade in at the bottom of each panel.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: Dark navy `#0B1120` (visible briefly during slide-in)
- No grid lines

### Chart/Visual Elements
- **Left Panel:** Ocean sunset footage (`veo/04_veo_broll.mp4`), 960×1080, left half
  - Label: "Ocean · Sunset" — bottom-center of left panel, over semi-transparent bar
- **Right Panel:** Forest canopy footage (`veo/05_veo_cutaway.mp4`), 960×1080, right half
  - Label: "Forest · Canopy" — bottom-center of right panel, over semi-transparent bar
- **Vertical Divider:** 2px line, `#C9A84C` (gold), full height, centered at x=960
- **Label Bars:** `rgba(11,17,32,0.7)` background, 48px tall, bottom of each panel

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Left panel slides in from -960px (off-screen left) to x=0. Right panel slides in from 1920px (off-screen right) to x=960. Both use `easeOutCubic`.
2. **Frame 15–20 (0.5–0.67s):** Vertical divider line draws from top to bottom at center.
3. **Frame 20–30 (0.67–1.0s):** Label bars slide up from bottom of each panel. Text fades in.
4. **Frame 30–45 (1.0–1.5s):** Hold on full split composition. Both videos continue playing.

### Typography
- Panel labels: Inter SemiBold, 24px, `#FFFFFF`
- Separator dot: Inter Regular, 24px, `#C9A84C`

### Easing
- Panel slide-in: `easeOutCubic`
- Divider draw: `easeInOutQuad`
- Label fade-in: `easeOutQuad`
- Label bar slide-up: `easeOutQuad`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={45}>
  <AbsoluteFill style={{ backgroundColor: '#0B1120' }}>
    <SplitPanel side="left">
      <OffthreadVideo src={staticFile('veo_section/veo/04_veo_broll.mp4')} />
      <Sequence from={20}>
        <PanelLabel text="Ocean · Sunset" />
      </Sequence>
    </SplitPanel>
    <SplitPanel side="right">
      <OffthreadVideo src={staticFile('veo_section/veo/05_veo_cutaway.mp4')} />
      <Sequence from={20}>
        <PanelLabel text="Forest · Canopy" />
      </Sequence>
    </SplitPanel>
    <Sequence from={15}>
      <VerticalDivider color="#C9A84C" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "panels": [
    {
      "side": "left",
      "label": "Ocean · Sunset",
      "source": "veo/04_veo_broll.mp4"
    },
    {
      "side": "right",
      "label": "Forest · Canopy",
      "source": "veo/05_veo_cutaway.mp4"
    }
  ],
  "divider_color": "#C9A84C"
}
```

---
