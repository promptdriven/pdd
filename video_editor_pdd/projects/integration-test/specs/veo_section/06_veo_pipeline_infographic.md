[Remotion]

# Section 2.6: Veo Pipeline Infographic

**Tool:** Remotion
**Duration:** ~5s
**Timestamp:** 0:21 - 0:26

## Visual Description
An animated infographic showing the Veo generation pipeline as a horizontal flow diagram. Three rounded-rectangle nodes appear in sequence from left to right: "Prompt" → "Veo 3.1" → "Clip". Connecting arrows animate between nodes. Below each node, a small descriptor label provides context. The overall aesthetic is clean and technical, with a dark background and accent colors matching the section palette.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0D1117
- No grid lines

### Chart/Visual Elements
- **Node 1 ("Prompt"):** Rounded rectangle (240x80, border-radius 12px), fill #1B2838, border 2px #5B9BD5, centered at (380, 440)
  - Icon: text-cursor icon (20px, #5B9BD5) left of label
  - Descriptor: "Text description" at (380, 540), color #8B949E
- **Node 2 ("Veo 3.1"):** Rounded rectangle (240x80, border-radius 12px), fill #1B2838, border 2px #D4A843, centered at (960, 440)
  - Icon: sparkle icon (20px, #D4A843) left of label
  - Descriptor: "AI video model" at (960, 540), color #8B949E
- **Node 3 ("Clip"):** Rounded rectangle (240x80, border-radius 12px), fill #1B2838, border 2px #40916C, centered at (1540, 440)
  - Icon: play-circle icon (20px, #40916C) left of label
  - Descriptor: "5s footage" at (1540, 540), color #8B949E
- **Arrow 1:** From (500, 440) → (840, 440), stroke #5B9BD5, 2px, arrowhead at end
- **Arrow 2:** From (1080, 440) → (1420, 440), stroke #D4A843, 2px, arrowhead at end
- **Section title:** "Veo Generation Pipeline" at top center (960, 120)

### Animation Sequence
1. **Frame 0-20 (0-0.67s):** Section title fades in from top
2. **Frame 15-40 (0.5-1.33s):** Node 1 scales in (0→1) with slight bounce
3. **Frame 35-55 (1.17-1.83s):** Arrow 1 draws left-to-right
4. **Frame 50-75 (1.67-2.5s):** Node 2 scales in (0→1) with slight bounce
5. **Frame 70-90 (2.33-3s):** Arrow 2 draws left-to-right
6. **Frame 85-110 (2.83-3.67s):** Node 3 scales in (0→1) with slight bounce
7. **Frame 40-60 (1.33-2s):** Descriptor 1 fades in
8. **Frame 75-95 (2.5-3.17s):** Descriptor 2 fades in
9. **Frame 110-130 (3.67-4.33s):** Descriptor 3 fades in
10. **Frame 130-150 (4.33-5s):** Hold complete diagram

### Typography
- Section title: Inter Bold, 36px, #FFFFFF
- Node labels: Inter SemiBold, 26px, #FFFFFF
- Descriptor labels: Inter Regular, 18px, #8B949E

### Easing
- Node scale-in: `easeOutBack`
- Arrow draw: `easeInOutCubic`
- Fade-ins: `easeOutCubic`

## Narration Sync
> (No narration — visual explanation of the Veo pipeline as a closing infographic)

## Code Structure (Remotion)
```typescript
<Sequence from={630} durationInFrames={150}>
  <Background color="#0D1117" />
  <Sequence from={0}>
    <FadeIn><SectionTitle text="Veo Generation Pipeline" /></FadeIn>
  </Sequence>
  <Sequence from={15}>
    <PipelineNode label="Prompt" icon="text-cursor" borderColor="#5B9BD5" x={380} />
  </Sequence>
  <Sequence from={35}>
    <Arrow from={[500, 440]} to={[840, 440]} color="#5B9BD5" />
  </Sequence>
  <Sequence from={50}>
    <PipelineNode label="Veo 3.1" icon="sparkle" borderColor="#D4A843" x={960} />
  </Sequence>
  <Sequence from={70}>
    <Arrow from={[1080, 440]} to={[1420, 440]} color="#D4A843" />
  </Sequence>
  <Sequence from={85}>
    <PipelineNode label="Clip" icon="play-circle" borderColor="#40916C" x={1540} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "pipeline_nodes": [
    { "label": "Prompt", "icon": "text-cursor", "color": "#5B9BD5", "descriptor": "Text description" },
    { "label": "Veo 3.1", "icon": "sparkle", "color": "#D4A843", "descriptor": "AI video model" },
    { "label": "Clip", "icon": "play-circle", "color": "#40916C", "descriptor": "5s footage" }
  ]
}
```

---
