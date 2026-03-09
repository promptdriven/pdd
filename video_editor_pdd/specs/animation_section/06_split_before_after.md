[split:]

# Section 1.6: Split Before/After Comparison

**Tool:** Remotion
**Duration:** ~4s
**Timestamp:** 0:23 - 0:27

## Visual Description
A split-screen comparison layout divided by a vertical center line. The left half shows the "Before" state — the original blue circle on a dark background — and the right half shows the "After" state — the green square at its final resting position. A bold divider line separates the two halves, with "BEFORE" and "AFTER" labels at the top of each panel. The divider slides in from the top, revealing each side simultaneously.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Left half #111827, right half #111827 (matching, with a subtle 1-shade difference: right is #0F172A for visual distinction)
- Grid lines: None

### Chart/Visual Elements
- Left panel (0-959px): Blue circle, 160px diameter, fill #3B82F6, centered at (480, 540)
- Right panel (961-1920px): Green square, 160x160px, fill #22C55E, centered at (1440, 540)
- Vertical divider: 3px solid #F8FAFC (slate-50), from (960, 0) to (960, 1080)
- "BEFORE" label: Top-left panel, positioned at (480, 80), centered
- "AFTER" label: Top-right panel, positioned at (1440, 80), centered
- Subtle vignette on each panel edge (inner shadow, 40px)

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Vertical divider slides down from top (y: -1080 → 0). Both panels are masked/hidden until divider arrives.
2. **Frame 15-40 (0.5-1.33s):** Left panel fades in — blue circle scales from 0.8 → 1.0 with opacity 0% → 100%. "BEFORE" label fades in.
3. **Frame 20-45 (0.67-1.5s):** Right panel fades in — green square scales from 0.8 → 1.0 with opacity 0% → 100%. "AFTER" label fades in.
4. **Frame 45-120 (1.5-4.0s):** Hold — both panels fully visible, static layout for viewer to absorb the comparison.

### Typography
- Panel labels: Inter Bold, 28px, #F8FAFC (slate-50), uppercase, letter-spacing 4px
- No additional text

### Easing
- Divider slide: `easeOutCubic`
- Panel reveals: `easeOutQuad`
- Shape scale-in: `easeOutCubic`

## Narration Sync
> (Bridge visual — no direct narration; visual recap of the transformation)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill>
    <Sequence from={15}>
      <LeftPanel>
        <Circle radius={80} fill="#3B82F6" />
        <PanelLabel text="BEFORE" />
      </LeftPanel>
    </Sequence>
    <Sequence from={20}>
      <RightPanel>
        <Square size={160} fill="#22C55E" />
        <PanelLabel text="AFTER" />
      </RightPanel>
    </Sequence>
    <Sequence from={0} durationInFrames={15}>
      <VerticalDivider />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "panels": {
    "left": {
      "label": "BEFORE",
      "background": "#111827",
      "shape": { "type": "circle", "radius": 80, "fill": "#3B82F6" }
    },
    "right": {
      "label": "AFTER",
      "background": "#0F172A",
      "shape": { "type": "square", "size": 160, "fill": "#22C55E" }
    }
  },
  "divider": {
    "color": "#F8FAFC",
    "width": 3
  }
}
```

---
