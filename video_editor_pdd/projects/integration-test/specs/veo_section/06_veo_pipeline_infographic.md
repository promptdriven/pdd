[Remotion]

# Section 2.6: Veo Pipeline Infographic

**Tool:** Remotion
**Duration:** ~0.03s (1 frame transition beat)
**Timestamp:** 0:05 - 0:05

## Visual Description
A compact infographic showing the Veo video generation pipeline as a horizontal flowchart. Four nodes connected by animated arrows illustrate the process: "Script" → "Veo Prompt" → "AI Video" → "Remotion Composite". Each node is a rounded rectangle with an icon and label. This beat is a brief transitional flash — it appears for approximately 1 frame as visual punctuation. The design uses a dark tech-blueprint aesthetic with neon accent lines.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0A1628 with subtle dot-grid pattern (dots at 40px intervals, color rgba(77,168,218,0.1))
- Grid: Dot pattern only

### Chart/Visual Elements
- **Pipeline nodes (4):**
  - Node 1: "Script" at x=200, y=440 — icon: document, bg #1B3A5C, border #4DA8DA, size 200x200
  - Node 2: "Veo Prompt" at x=560, y=440 — icon: sparkle, bg #1B3A5C, border #4DA8DA, size 200x200
  - Node 3: "AI Video" at x=920, y=440 — icon: film, bg #1B3A5C, border #6FCF97, size 200x200
  - Node 4: "Remotion Composite" at x=1280, y=440 — icon: layers, bg #1B3A5C, border #F2C94C, size 200x200
- **Connecting arrows (3):**
  - Arrow 1→2: Horizontal line from x=400 to x=560, y=540, color #4DA8DA, dashed
  - Arrow 2→3: Horizontal line from x=760 to x=920, y=540, color #4DA8DA, dashed
  - Arrow 3→4: Horizontal line from x=1120 to x=1280, y=540, color #6FCF97, dashed
- **Title:** "VIDEO GENERATION PIPELINE" at top center y=100
- **Accent glow:** Each node has a subtle outer glow matching its border color (blur 16px, opacity 0.3)

### Animation Sequence
1. **Frame 0-1 (0-0.03s):** All elements rendered instantly (single-frame beat). No animation — static infographic flash.

### Typography
- Title: Inter Bold, 36px, #FFFFFF, letter-spacing 8px
- Node labels: Inter SemiBold, 16px, #FFFFFF
- Node icons: Lucide icon set, 40px, matching border color

### Easing
- None (single-frame display)

## Narration Sync
> (Transitional beat — no dedicated narration)

## Code Structure (Remotion)
```typescript
<Sequence from={154} durationInFrames={1}>
  <AbsoluteFill style={{ backgroundColor: '#0A1628' }}>
    <DotGridPattern spacing={40} color="rgba(77,168,218,0.1)" />
    <HeaderText text="VIDEO GENERATION PIPELINE" />
    <PipelineNode x={200} label="Script" icon="document" borderColor="#4DA8DA" />
    <PipelineArrow from={400} to={560} color="#4DA8DA" />
    <PipelineNode x={560} label="Veo Prompt" icon="sparkle" borderColor="#4DA8DA" />
    <PipelineArrow from={760} to={920} color="#4DA8DA" />
    <PipelineNode x={920} label="AI Video" icon="film" borderColor="#6FCF97" />
    <PipelineArrow from={1120} to={1280} color="#6FCF97" />
    <PipelineNode x={1280} label="Remotion Composite" icon="layers" borderColor="#F2C94C" />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "title": "VIDEO GENERATION PIPELINE",
  "nodes": [
    { "label": "Script", "icon": "document", "color": "#4DA8DA" },
    { "label": "Veo Prompt", "icon": "sparkle", "color": "#4DA8DA" },
    { "label": "AI Video", "icon": "film", "color": "#6FCF97" },
    { "label": "Remotion Composite", "icon": "layers", "color": "#F2C94C" }
  ]
}
```
