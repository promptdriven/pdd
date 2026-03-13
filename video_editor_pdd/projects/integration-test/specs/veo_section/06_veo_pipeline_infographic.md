[Remotion] Veo Generation Pipeline Infographic

# Section 2.6: Veo Generation Pipeline Infographic

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:16 – 0:21

## Visual Description
An animated infographic showing the three-stage Veo generation pipeline as a left-to-right flow diagram. A section title "Veo Generation Pipeline" fades in at the top, then three rounded-rectangle nodes appear one by one with a spring-bounce effect. Connecting arrows draw between nodes, and small descriptor labels fade in beneath each node. The nodes are colour-coded: blue for Prompt, gold for Veo 3.1, and green for Clip.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0D1117`

### Chart/Visual Elements
- **Section title:** "Veo Generation Pipeline" centred at Y=120px
- **Node 1 — Prompt:** 240x80px rounded rect (border-radius 12px), border `#5B9BD5` 2px, fill `#1B2838`, text-cursor icon, label "Prompt", descriptor "Text description", X=380px
- **Node 2 — Veo 3.1:** Same dimensions, border `#D4A843`, sparkle icon, label "Veo 3.1", descriptor "AI video model", X=960px
- **Node 3 — Clip:** Same dimensions, border `#40916C`, play-circle icon, label "Clip", descriptor "5s footage", X=1540px
- **Arrow 1:** From X=500 to X=840, stroke `#5B9BD5` 2px, arrowhead 10px
- **Arrow 2:** From X=1080 to X=1420, stroke `#D4A843` 2px, arrowhead 10px
- All nodes and arrows at Y=440px; descriptors at Y=540px

### Animation Sequence
1. **Frame 0–20 (0–0.67s):** Section title fades in (opacity 0 → 1) and slides down (translateY -20px → 0) with `easeOutCubic`
2. **Frame 15–40 (0.5–1.33s):** Node 1 scales in (0 → 1) with `easeOut(back(1.7))` bounce; opacity snaps 0 → 1 at frame 15–20
3. **Frame 35–55 (1.17–1.83s):** Arrow 1 draws left-to-right (progress 0 → 1) with `easeInOutCubic`; arrowhead appears at 80% progress
4. **Frame 40–60 (1.33–2.0s):** Descriptor 1 "Text description" fades in with `easeOutCubic`
5. **Frame 50–75 (1.67–2.5s):** Node 2 scales in with same bounce easing
6. **Frame 70–90 (2.33–3.0s):** Arrow 2 draws left-to-right with `easeInOutCubic`
7. **Frame 75–95 (2.5–3.17s):** Descriptor 2 "AI video model" fades in
8. **Frame 85–110 (2.83–3.67s):** Node 3 scales in with same bounce easing
9. **Frame 110–130 (3.67–4.33s):** Descriptor 3 "5s footage" fades in

### Typography
- Section title: Inter, 36px, weight 700, `#FFFFFF`
- Node labels: Inter, 26px, weight 600, `#FFFFFF`
- Descriptors: Inter, 18px, weight 400, `#8B949E`
- Icon size: 20px

### Easing
- Title entrance: `Easing.out(Easing.cubic)`
- Node scale: `Easing.out(Easing.back(1.7))`
- Arrow draw: `Easing.inOut(Easing.cubic)`
- Descriptor fade: `Easing.out(Easing.cubic)`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={150}>
  <AbsoluteFill style={{ backgroundColor: "#0D1117" }}>
    <SectionTitle text="Veo Generation Pipeline" y={120} />
    <Sequence from={15}>
      <PipelineNode icon="textCursor" label="Prompt" color="#5B9BD5" x={380} />
    </Sequence>
    <Sequence from={35}>
      <PipelineArrow from={500} to={840} color="#5B9BD5" />
    </Sequence>
    <Sequence from={50}>
      <PipelineNode icon="sparkle" label="Veo 3.1" color="#D4A843" x={960} />
    </Sequence>
    <Sequence from={70}>
      <PipelineArrow from={1080} to={1420} color="#D4A843" />
    </Sequence>
    <Sequence from={85}>
      <PipelineNode icon="playCircle" label="Clip" color="#40916C" x={1540} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "Veo Generation Pipeline",
  "nodes": [
    {
      "id": "prompt",
      "icon": "textCursor",
      "label": "Prompt",
      "descriptor": "Text description",
      "borderColor": "#5B9BD5",
      "x": 380
    },
    {
      "id": "veo",
      "icon": "sparkle",
      "label": "Veo 3.1",
      "descriptor": "AI video model",
      "borderColor": "#D4A843",
      "x": 960
    },
    {
      "id": "clip",
      "icon": "playCircle",
      "label": "Clip",
      "descriptor": "5s footage",
      "borderColor": "#40916C",
      "x": 1540
    }
  ],
  "arrows": [
    { "from": 500, "to": 840, "color": "#5B9BD5" },
    { "from": 1080, "to": 1420, "color": "#D4A843" }
  ],
  "nodeSize": { "width": 240, "height": 80 },
  "nodeFill": "#1B2838",
  "nodeY": 440,
  "descriptorY": 540
}
```

---
