[Remotion]

# Section 2.8: Veo Technology Callout

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:21 - 0:24

## Visual Description
An informational callout card slides in from the bottom of the frame, explaining how Veo technology generates the footage. The card is a semi-transparent dark panel with a schematic diagram showing "Text Prompt → Veo AI → Video Clip" as a horizontal flow with connecting arrows. Each node is a rounded box with an icon. The card provides technical context about the AI video generation pipeline.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Transparent overlay on top of Veo footage layer

### Chart/Visual Elements
- Card panel: Rounded rectangle (borderRadius 20px), centered horizontally, Y=680, 800px x 280px
  - Background: rgba(15, 15, 15, 0.85) with backdrop-blur(16px)
  - Border: 1px solid rgba(255, 255, 255, 0.08)
- Flow diagram (3 nodes connected by arrows, centered inside card):
  - Node 1: "Text Prompt" — rounded box 160x80px, border #818CF8 (indigo), icon: text cursor
  - Node 2: "Veo AI" — rounded box 160x80px, border #F59E0B (amber), icon: sparkle, filled background rgba(245, 158, 11, 0.15)
  - Node 3: "Video Clip" — rounded box 160x80px, border #34D399 (emerald), icon: film frame
  - Arrows: 60px connecting lines between nodes, 2px, #FFFFFF at 40% opacity, with arrowhead
- Header text: "How Veo Works" above the flow diagram

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Card panel slides up from Y=1100 (offscreen) to Y=680. Opacity 0% to 100%.
2. **Frame 20-35 (0.67-1.17s):** Node 1 ("Text Prompt") fades in and scales from 0.8 to 1.0.
3. **Frame 30-40 (1-1.33s):** Arrow 1 draws left-to-right. Node 2 ("Veo AI") fades in and scales.
4. **Frame 40-50 (1.33-1.67s):** Arrow 2 draws left-to-right. Node 3 ("Video Clip") fades in and scales.
5. **Frame 50-75 (1.67-2.5s):** Hold — all elements visible. Veo AI node glows with a subtle amber pulse.
6. **Frame 75-90 (2.5-3s):** Entire card fades out and slides down to Y=720.

### Typography
- Header: Inter Bold, 22px, #FFFFFF, letter-spacing 1px
- Node labels: Inter SemiBold, 16px, #FFFFFF
- No additional text

### Easing
- Card slide in: `easeOutCubic`
- Node scale: `easeOutBack`
- Arrow draw: `easeOutQuad`
- Card fade out: `easeInQuad`

## Narration Sync
> (No narration — visual explanation beat between segments)

## Code Structure (Remotion)
```typescript
<Sequence from={630} durationInFrames={90}>
  <CalloutCard position={{ y: 680 }} width={800} height={280}>
    <CardHeader text="How Veo Works" />
    <Sequence from={20}>
      <FlowDiagram
        nodes={[
          { label: "Text Prompt", icon: "cursor", borderColor: "#818CF8" },
          { label: "Veo AI", icon: "sparkle", borderColor: "#F59E0B", filled: true },
          { label: "Video Clip", icon: "film", borderColor: "#34D399" },
        ]}
        arrowColor="rgba(255, 255, 255, 0.4)"
        staggerFrames={10}
      />
    </Sequence>
  </CalloutCard>
</Sequence>
```

## Data Points
```json
{
  "nodes": [
    { "label": "Text Prompt", "color": "#818CF8" },
    { "label": "Veo AI", "color": "#F59E0B" },
    { "label": "Video Clip", "color": "#34D399" }
  ],
  "header": "How Veo Works"
}
```

---
