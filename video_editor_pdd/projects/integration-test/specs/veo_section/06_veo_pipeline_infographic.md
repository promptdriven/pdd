[Remotion]

# Section 2.6: Veo Pipeline Infographic

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:14 – 0:15

## Visual Description
An animated infographic illustrating the Veo video generation pipeline as a horizontal flow diagram. Three nodes — "Prompt", "Veo Model", and "Video Output" — are connected by directional arrows. Each node is a rounded card with an icon and label. The nodes appear sequentially left-to-right, with arrows drawing between them. A subtle particle trail follows each arrow to convey data flow. The visualization explains how the AI-generated footage in this section was produced.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark charcoal (#111827)
- Grid lines: Dot grid pattern, #FFFFFF at 3% opacity, spacing 40px

### Chart/Visual Elements
- **Node 1 — "Prompt" (x: 200, y: 440):**
  - Rounded rect: 280x200px, radius 16px, fill #1E293B, border 2px #6366F1 (indigo)
  - Icon: Text cursor glyph, 48px, color #6366F1
  - Label: "Text Prompt" beneath icon
- **Node 2 — "Veo Model" (x: 820, y: 440):**
  - Rounded rect: 280x200px, radius 16px, fill #1E293B, border 2px #8B5CF6 (violet)
  - Icon: Brain/AI glyph, 48px, color #8B5CF6
  - Label: "Veo Model" beneath icon
- **Node 3 — "Video Output" (x: 1440, y: 440):**
  - Rounded rect: 280x200px, radius 16px, fill #1E293B, border 2px #10B981 (emerald)
  - Icon: Play button glyph, 48px, color #10B981
  - Label: "Video Output" beneath icon
- **Arrow 1 (Node 1→2):**
  - Path from (480, 540) → (820, 540), stroke #6366F1→#8B5CF6 gradient, 3px, arrowhead at end
- **Arrow 2 (Node 2→3):**
  - Path from (1100, 540) → (1440, 540), stroke #8B5CF6→#10B981 gradient, 3px, arrowhead at end
- **Section title:** "How Veo Works" — top center at (960, 80)

### Animation Sequence
1. **Frame 0–4 (0–0.13s):** Section title fades in (opacity 0→1)
2. **Frame 4–10 (0.13–0.33s):** Node 1 scales in from 0.8→1.0 with opacity 0→1
3. **Frame 10–14 (0.33–0.47s):** Arrow 1 draws left-to-right (strokeDashoffset animation)
4. **Frame 14–20 (0.47–0.67s):** Node 2 scales in from 0.8→1.0 with opacity 0→1
5. **Frame 20–24 (0.67–0.8s):** Arrow 2 draws left-to-right
6. **Frame 24–28 (0.8–0.93s):** Node 3 scales in from 0.8→1.0 with opacity 0→1. Node 3 border pulses once (opacity 100%→60%→100%) to emphasize the output
7. **Frame 28–30 (0.93–1.0s):** Hold — full pipeline visible

### Typography
- Section title: Inter Bold, 36px, white (#FFFFFF)
- Node labels: Inter SemiBold, 18px, white (#FFFFFF)

### Easing
- Node scale-in: `easeOutBack` (slight overshoot for pop)
- Arrow draw: `easeInOutQuad`
- Title fade: `easeOutCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <AbsoluteFill style={{ backgroundColor: "#111827" }}>
    <DotGrid spacing={40} opacity={0.03} />
    <SectionTitle text="How Veo Works" y={80} />

    <Sequence from={4}>
      <PipelineNode
        x={200} y={440}
        icon="text-cursor" label="Text Prompt"
        borderColor="#6366F1"
      />
    </Sequence>

    <Sequence from={10}>
      <FlowArrow from={[480, 540]} to={[820, 540]} gradientColors={["#6366F1", "#8B5CF6"]} />
    </Sequence>

    <Sequence from={14}>
      <PipelineNode
        x={820} y={440}
        icon="brain" label="Veo Model"
        borderColor="#8B5CF6"
      />
    </Sequence>

    <Sequence from={20}>
      <FlowArrow from={[1100, 540]} to={[1440, 540]} gradientColors={["#8B5CF6", "#10B981"]} />
    </Sequence>

    <Sequence from={24}>
      <PipelineNode
        x={1440} y={440}
        icon="play" label="Video Output"
        borderColor="#10B981"
        pulse={true}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "pipeline_steps": [
    { "id": "prompt", "label": "Text Prompt", "color": "#6366F1", "icon": "text-cursor" },
    { "id": "model", "label": "Veo Model", "color": "#8B5CF6", "icon": "brain" },
    { "id": "output", "label": "Video Output", "color": "#10B981", "icon": "play" }
  ],
  "arrows": [
    { "from": "prompt", "to": "model" },
    { "from": "model", "to": "output" }
  ]
}
```

---
