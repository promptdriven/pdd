[Remotion]

# Section 1.6: Debt Layers Zoom — Code Complexity vs. Context Rot

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 2:49 - 3:07

## Visual Description

The camera zooms into the shaded debt area from the code cost chart. As we zoom in, the monolithic amber area separates into two distinct layers:

1. **"Code Complexity" (darker amber, lower layer):** Dense, solid — represents traditional technical debt (spaghetti code, dependency tangles, unclear interfaces).
2. **"Context Rot" (lighter amber with noise texture, upper layer):** Has a subtle static/noise texture overlay — represents the AI-specific problem of models losing performance as codebases grow beyond context windows.

The separation into two layers is the key reveal — there's a kind of debt that's unique to AI-assisted development, and it's growing on top of the familiar kind.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Debt Area (pre-zoom)
- Shaded area from spec 03, `#D9944A` at 0.12

#### Lower Layer — Code Complexity
- Fill: `#D9944A` at 0.18 (darker)
- Label: "Code Complexity" — Inter 16px, bold (700), `#D9944A`
- Texture: Smooth, no noise

#### Upper Layer — Context Rot
- Fill: `#F59E0B` at 0.12 (lighter)
- Label: "Context Rot" — Inter 16px, bold (700), `#F59E0B`
- Texture: Subtle noise/static overlay (`#FFFFFF` at 0.03, 2px grain)
- Noise animates slowly — drifting static effect

#### Zoom Region
- Target: Right portion of debt area (2022-2026 range)
- Zoom factor: ~3× into the shaded region

### Animation Sequence
1. **Frame 0-90 (0-3s):** Camera zooms into the debt area. The chart periphery fades, debt area fills the frame.
2. **Frame 90-180 (3-6s):** The monolithic amber area cracks and separates into two horizontal layers. A hairline gap appears between them.
3. **Frame 180-270 (6-9s):** Lower layer darkens and takes "Code Complexity" label. Upper layer lightens and takes noise texture + "Context Rot" label.
4. **Frame 270-540 (9-18s):** Hold. Context Rot layer pulses with subtle noise animation. Both labels visible. The upper layer is slightly taller, suggesting it's growing faster.

### Typography
- Layer labels: Inter, 16px, bold (700), respective colors
- Labels positioned centered within their respective layers

### Easing
- Camera zoom: `easeInOut(cubic)` over 90 frames
- Layer separation: `easeOut(quad)` over 60 frames — smooth crack open
- Label fade-in: `easeOut(quad)` over 20 frames
- Noise drift: constant, 0.5px per frame lateral movement

## Narration Sync
> "But there's a second kind of debt hiding in there. One that's specific to AI-assisted development."
> "When your codebase is small, AI tools are brilliant. The context window — what the model can actually see — covers almost everything."

Segments: `part1_economics_013`, `part1_economics_014`

- **163.06s** (seg 013): Zoom begins — "there's a second kind of debt"
- **168.62s** (seg 013 ends): Layers separating
- **168.86s** (seg 014): "When your codebase is small" — layers fully visible, transition to context window
- **181.54s** (seg 014 ends): Hold, preparing for context window morphing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Zoom into debt area */}
    <Sequence from={0}>
      <ScaleTransition from={1.0} to={3.0}
        origin={{ x: 1200, y: 400 }}
        duration={90} easing="easeInOutCubic" />
    </Sequence>

    {/* Layer separation */}
    <Sequence from={90}>
      <LayerSplit
        sourceArea="debt_area"
        lower={{
          color: "#D9944A", opacity: 0.18,
          label: "Code Complexity"
        }}
        upper={{
          color: "#F59E0B", opacity: 0.12,
          label: "Context Rot",
          noiseOverlay: { color: "#FFFFFF", opacity: 0.03, grain: 2 }
        }}
        splitDuration={90}
        gapHeight={4}
      />
    </Sequence>

    {/* Labels */}
    <Sequence from={180}>
      <FadeIn duration={20}>
        <Text text="Code Complexity" color="#D9944A"
          size={16} weight={700} y={550} />
        <Text text="Context Rot" color="#F59E0B"
          size={16} weight={700} y={350} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "debt_layer_zoom",
  "chartRef": "code_cost_generate_vs_patch",
  "layers": [
    {
      "id": "code_complexity",
      "label": "Code Complexity",
      "color": "#D9944A",
      "opacity": 0.18,
      "position": "lower",
      "description": "Traditional technical debt: spaghetti code, dependency tangles"
    },
    {
      "id": "context_rot",
      "label": "Context Rot",
      "color": "#F59E0B",
      "opacity": 0.12,
      "position": "upper",
      "noiseTexture": true,
      "description": "AI-specific: model performance degrades as codebase exceeds context window"
    }
  ],
  "narrationSegments": ["part1_economics_013", "part1_economics_014"]
}
```

---
