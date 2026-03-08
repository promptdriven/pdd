[Remotion]

# Section 1.5: Animation Engine Flow Diagram

**Tool:** Remotion
**Duration:** ~2.5s (75 frames)
**Timestamp:** 0:03 - 0:06

## Visual Description
An animated node-and-edge flow diagram showing how the Remotion rendering pipeline works. Three nodes appear left-to-right: "Spec" (document icon), "Remotion" (gear icon), and "Video" (play icon). Connecting arrows draw between them sequentially, with a pulsing data-flow highlight that travels along each arrow. The diagram sits on a dark charcoal background with a subtle grid pattern.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Solid #1E1E2E (dark charcoal)
- Grid lines: 40px grid, color #2A2A3E at 20% opacity

### Chart/Visual Elements
- **Node 1 — "Spec":** Rounded rectangle 200x120px at position (280, 480), fill #3B82F6, border-radius 16px, document icon (white, 40px) centered above label
- **Node 2 — "Remotion":** Rounded rectangle 200x120px at position (860, 480), fill #8B5CF6, border-radius 16px, gear icon (white, 40px) centered above label
- **Node 3 — "Video":** Rounded rectangle 200x120px at position (1440, 480), fill #22C55E, border-radius 16px, play triangle icon (white, 40px) centered above label
- **Arrow 1:** Horizontal line from (480, 540) to (860, 540), 4px stroke, color #64748B, arrowhead at end
- **Arrow 2:** Horizontal line from (1060, 540) to (1440, 540), 4px stroke, color #64748B, arrowhead at end
- **Data pulse:** Glowing circle (12px, white, blur 8px) that travels along each arrow path
- **Node labels:** Centered below icons, inside the rounded rectangles

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Node 1 ("Spec") fades in and scales from 0.8→1.0 with bounce
2. **Frame 10-30 (0.33-1.0s):** Arrow 1 draws left-to-right (stroke-dashoffset animation)
3. **Frame 20-35 (0.67-1.17s):** Node 2 ("Remotion") fades in and scales from 0.8→1.0 with bounce
4. **Frame 30-50 (1.0-1.67s):** Arrow 2 draws left-to-right
5. **Frame 40-55 (1.33-1.83s):** Node 3 ("Video") fades in and scales from 0.8→1.0 with bounce
6. **Frame 50-75 (1.67-2.5s):** Data pulse travels along Arrow 1 then Arrow 2 in sequence, looping once

### Typography
- Node labels: Inter, 24px, semibold (600), #FFFFFF
- Section heading (optional): Inter, 36px, bold, #E2E8F0, top-left at (72, 72)

### Easing
- Node scale-in: `easeOutBack` (slight overshoot bounce)
- Arrow draw: `easeInOutQuad`
- Data pulse travel: `linear` (constant speed along path)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

This diagram appears during segment 2 (3.0s-6.0s), visually explaining the Remotion-only pipeline — specs go in, Remotion processes them, video frames come out.

## Code Structure (Remotion)
```typescript
<Sequence from={90} durationInFrames={75}>
  <AbsoluteFill style={{ backgroundColor: '#1E1E2E' }}>
    <GridOverlay spacing={40} color="#2A2A3E" opacity={0.2} />

    <Sequence from={0} durationInFrames={15}>
      <FlowNode x={280} y={480} label="Spec" icon="document" color="#3B82F6" />
    </Sequence>

    <Sequence from={10} durationInFrames={20}>
      <AnimatedArrow from={[480, 540]} to={[860, 540]} strokeColor="#64748B" />
    </Sequence>

    <Sequence from={20} durationInFrames={15}>
      <FlowNode x={860} y={480} label="Remotion" icon="gear" color="#8B5CF6" />
    </Sequence>

    <Sequence from={30} durationInFrames={20}>
      <AnimatedArrow from={[1060, 540]} to={[1440, 540]} strokeColor="#64748B" />
    </Sequence>

    <Sequence from={40} durationInFrames={15}>
      <FlowNode x={1440} y={480} label="Video" icon="play" color="#22C55E" />
    </Sequence>

    <Sequence from={50} durationInFrames={25}>
      <DataPulse path={[[480, 540], [860, 540], [1060, 540], [1440, 540]]} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "nodes": [
    { "id": "spec", "label": "Spec", "x": 280, "y": 480, "color": "#3B82F6", "icon": "document" },
    { "id": "remotion", "label": "Remotion", "x": 860, "y": 480, "color": "#8B5CF6", "icon": "gear" },
    { "id": "video", "label": "Video", "x": 1440, "y": 480, "color": "#22C55E", "icon": "play" }
  ],
  "edges": [
    { "from": "spec", "to": "remotion" },
    { "from": "remotion", "to": "video" }
  ]
}
```

---
