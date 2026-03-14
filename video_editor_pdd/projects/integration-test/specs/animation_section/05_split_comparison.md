[split:]

# Section 1.5: Split Comparison

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:04.7 - 0:05.7

## Visual Description
A split-screen comparison layout slides into view. The left half has a dark blue (#1E3A5F) background showing a static circle (representing "Before" — the original shape). The right half has a dark indigo (#312E81) background showing the morphed rounded square (representing "After" — the transformed shape). A vertical white divider line (2px) separates the two halves. Labels "Before" and "After" appear beneath each shape. The entire layout slides up from below the canvas.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Left half #1E3A5F, Right half #312E81
- Grid lines: None

### Chart/Visual Elements
- Vertical divider: x=960, full height, 2px wide, white (#FFFFFF) at 60% opacity
- Left panel: 960x1080, background #1E3A5F
  - Circle: centered at (480, 440), 80px radius, fill #3B82F6, no stroke
  - Label "Before": centered at (480, 580)
- Right panel: 960x1080, background #312E81
  - Rounded square: centered at (1440, 440), 120x120px, borderRadius 12px, fill #6366F1
  - Label "After": centered at (1440, 580)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Entire layout slides up from y=1080 to y=0; divider line simultaneously fades in from 0% to 60% opacity
2. **Frame 12-22 (0.4-0.73s):** "Before" label fades in on left side
3. **Frame 15-25 (0.5-0.83s):** "After" label fades in on right side
4. **Frame 25-30 (0.83-1.0s):** Hold at full visibility

### Typography
- Labels: Inter SemiBold, 24px, white (#FFFFFF) at 90% opacity
- No title text

### Easing
- Slide up: `easeOutCubic`
- Label fade: `easeOutQuad`
- Divider fade: `easeInOutQuad`

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <SlideUp>
    <SplitLayout dividerColor="#FFFFFF" dividerOpacity={0.6}>
      <LeftPanel background="#1E3A5F">
        <Circle radius={80} color="#3B82F6" />
        <Sequence from={12}>
          <FadeIn><Label text="Before" /></FadeIn>
        </Sequence>
      </LeftPanel>
      <RightPanel background="#312E81">
        <RoundedSquare size={120} radius={12} color="#6366F1" />
        <Sequence from={15}>
          <FadeIn><Label text="After" /></FadeIn>
        </Sequence>
      </RightPanel>
    </SplitLayout>
  </SlideUp>
</Sequence>
```

## Data Points
```json
{
  "comparison": {
    "left": {
      "label": "Before",
      "shape": "circle",
      "color": "#3B82F6",
      "background": "#1E3A5F"
    },
    "right": {
      "label": "After",
      "shape": "roundedSquare",
      "color": "#6366F1",
      "background": "#312E81"
    }
  }
}
```

---

<!-- ANNOTATION_UPDATE_START: test-batch-ann-1773466645087 -->
## Annotation Update
Requested change: Change the primary background accent in Animation Section to #00FF00.
Technical assessment: The current color treatment should shift to a clearly visible green accent.
- Update the background accent color to #00FF00
<!-- ANNOTATION_UPDATE_END: test-batch-ann-1773466645087 -->
