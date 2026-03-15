[Remotion]

# Section 2.5: Veo Pipeline Infographic

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:13.5 – 0:15.5

## Visual Description
A three-step horizontal pipeline infographic explaining the Veo AI generation workflow. Three nodes appear in sequence — "Prompt" (text icon), "Veo AI" (sparkle icon), and "Clip" (film icon) — connected by animated arrow paths. Each node is a rounded card with an icon and label. Connecting arrows animate between nodes with a flowing particle effect. A gradient overlay at the bottom anchors the composition.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: Dark navy `#0B1120`
- Gradient overlay at bottom: `linear-gradient(transparent, rgba(11,17,32,0.9))` lower 30%

### Chart/Visual Elements
- **Node 1 — Prompt:** Rounded rect card (160×160px), centered at x=330, y=480
  - Icon: Text/document icon, 48px, `#C9A84C`
  - Label: "Prompt" below card
  - Card bg: `rgba(201,168,76,0.12)`, border: 1px `rgba(201,168,76,0.3)`
- **Node 2 — Veo AI:** Rounded rect card (160×160px), centered at x=870, y=480
  - Icon: Sparkle/magic icon, 48px, `#C9A84C`
  - Label: "Veo AI" below card
  - Card bg: `rgba(201,168,76,0.12)`, border: 1px `rgba(201,168,76,0.3)`
- **Node 3 — Clip:** Rounded rect card (160×160px), centered at x=1410, y=480
  - Icon: Film/clapperboard icon, 48px, `#C9A84C`
  - Label: "Clip" below card
  - Card bg: `rgba(201,168,76,0.12)`, border: 1px `rgba(201,168,76,0.3)`
- **Arrow Path 1:** From Node 1 right edge to Node 2 left edge, dashed line with animated dash offset
  - Stroke: `#C9A84C`, 2px, dash pattern `8 4`
  - Arrowhead: triangle at end, 10px
- **Arrow Path 2:** From Node 2 right edge to Node 3 left edge, same style
- **Flow Particles:** Small gold dots (3px) traveling along arrow paths, 2 particles per path

### Animation Sequence
1. **Frame 0–12 (0–0.4s):** Node 1 (Prompt) scales up from 0 to 1 with bounce. Icon fades in.
2. **Frame 12–22 (0.4–0.73s):** Arrow Path 1 draws from left to right. Flow particles begin traveling.
3. **Frame 22–34 (0.73–1.13s):** Node 2 (Veo AI) scales up from 0 to 1 with bounce. Sparkle icon pulses once.
4. **Frame 34–44 (1.13–1.47s):** Arrow Path 2 draws from left to right. Flow particles begin.
5. **Frame 44–54 (1.47–1.8s):** Node 3 (Clip) scales up from 0 to 1 with bounce.
6. **Frame 54–60 (1.8–2.0s):** All elements hold. Continuous particle flow on both arrows. Subtle glow pulse on all nodes.

### Typography
- Node labels: Inter SemiBold, 20px, `#FFFFFF`
- Step numbers (optional): Inter Regular, 12px, `rgba(255,255,255,0.5)`

### Easing
- Node scale-up: `easeOutBack` (overshoot bounce)
- Arrow draw: `easeInOutQuad`
- Particle flow: `linear` (constant speed)
- Icon fade: `easeOutQuad`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <AbsoluteFill style={{ backgroundColor: '#0B1120' }}>
    <GradientOverlay />
    <Sequence from={0}>
      <PipelineNode icon="text" label="Prompt" x={330} />
    </Sequence>
    <Sequence from={12}>
      <ArrowPath from={330} to={870} />
    </Sequence>
    <Sequence from={22}>
      <PipelineNode icon="sparkle" label="Veo AI" x={870} />
    </Sequence>
    <Sequence from={34}>
      <ArrowPath from={870} to={1410} />
    </Sequence>
    <Sequence from={44}>
      <PipelineNode icon="film" label="Clip" x={1410} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "pipeline_steps": [
    { "label": "Prompt", "icon": "text", "x": 330 },
    { "label": "Veo AI", "icon": "sparkle", "x": 870 },
    { "label": "Clip", "icon": "film", "x": 1410 }
  ],
  "arrow_style": {
    "stroke": "#C9A84C",
    "dash_pattern": "8 4",
    "particle_count": 2
  }
}
```

---
