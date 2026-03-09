[Remotion]

# Section 1.4: Shape Showcase Infographic

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:13 - 0:18

## Visual Description
An infographic-style showcase displaying the two key shapes from the section — the blue circle and the green square — side by side with labeled callouts. Each shape sits inside a rounded card with a subtle border, and animated stat labels appear beneath each: "Pulse Animation" under the circle, "Morph + Slide" under the square. A connecting dotted arrow flows from the circle card to the square card to illustrate the transformation sequence.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark slate (#0F172A)
- Grid lines: None

### Chart/Visual Elements
- Left card: 360x360px rounded rect (border-radius 16px), background #1E293B, border 1px solid #334155, centered at (560, 440)
  - Blue circle inside: 120px diameter, fill #3B82F6, centered within card
  - Label below card: "Pulse Animation"
- Right card: 360x360px rounded rect (border-radius 16px), background #1E293B, border 1px solid #334155, centered at (1360, 440)
  - Green square inside: 120x120px, fill #22C55E, centered within card
  - Label below card: "Morph + Slide"
- Connecting arrow: Dotted line (#475569) from right edge of left card (740, 440) to left edge of right card (1180, 440), with arrowhead pointing right
- Section subtitle: "Pure Remotion — No Veo Required" centered above cards at y=140

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Subtitle text fades in from above (translateY -30px → 0, opacity 0% → 100%).
2. **Frame 20-50 (0.67-1.67s):** Left card slides in from the left (translateX -200px → 0) with fade. Blue circle inside scales from 0 → 1.
3. **Frame 40-70 (1.33-2.33s):** Right card slides in from the right (translateX +200px → 0) with fade. Green square inside scales from 0 → 1.
4. **Frame 60-80 (2.0-2.67s):** Dotted connecting arrow draws from left to right (stroke-dashoffset animation).
5. **Frame 80-100 (2.67-3.33s):** Labels "Pulse Animation" and "Morph + Slide" fade in beneath their respective cards.
6. **Frame 100-150 (3.33-5.0s):** Hold — all elements visible and static.

### Typography
- Section subtitle: Inter SemiBold, 36px, #94A3B8 (slate-400), letter-spacing 1px
- Card labels: Inter Medium, 24px, #E2E8F0 (slate-200)

### Easing
- Card slide-in: `easeOutCubic`
- Shape scale-in: `easeOutBack`
- Arrow draw: `easeInOutQuad`
- Label fade: `easeOutQuad`

## Narration Sync
> (Bridge visual — no direct narration; plays between narration segments)

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    <Sequence from={0} durationInFrames={30}>
      <FadeInTitle text="Pure Remotion — No Veo Required" y={140} />
    </Sequence>
    <Sequence from={20} durationInFrames={40}>
      <SlideIn direction="left">
        <ShapeCard shape="circle" color="#3B82F6" label="Pulse Animation" />
      </SlideIn>
    </Sequence>
    <Sequence from={40} durationInFrames={40}>
      <SlideIn direction="right">
        <ShapeCard shape="square" color="#22C55E" label="Morph + Slide" />
      </SlideIn>
    </Sequence>
    <Sequence from={60} durationInFrames={20}>
      <DottedArrow from={[740, 440]} to={[1180, 440]} />
    </Sequence>
    <Sequence from={80} durationInFrames={20}>
      <FadeIn><Labels /></FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "cards": [
    {
      "shape": "circle",
      "color": "#3B82F6",
      "label": "Pulse Animation",
      "position": [560, 440]
    },
    {
      "shape": "square",
      "color": "#22C55E",
      "label": "Morph + Slide",
      "position": [1360, 440]
    }
  ],
  "subtitle": "Pure Remotion — No Veo Required"
}
```

---
