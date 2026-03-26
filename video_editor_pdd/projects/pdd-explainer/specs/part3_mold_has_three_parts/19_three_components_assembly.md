[Remotion]

# Section 3.19: Three Components Assembly — Complete Pipeline

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 4:26 - 4:40

## Visual Description

A pull-back view showing all three mold components working together in a single animated pipeline. The full mold cross-section is visible, now with all three regions active and connected by animated flow:

1. **Prompt** (teal nozzle) — natural language text flows in from the top
2. **Grounding** (purple material) — the material picks up style properties as it passes through
3. **Test Walls** (amber boundaries) — the liquid hits walls and is constrained into its final shape
4. **Code emerges** — clean output flows out at the bottom

The animation shows the complete journey: text enters → becomes styled material → fills the mold → constrained by walls → code appears. Labels track each stage.

Below: "Prompt + Tests + Grounding. Intent + Constraints + Style. Together, they form a complete specification."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Full Mold (all regions active)
- Centered at (960, 450), larger scale: 800×500px
- Nozzle: `#2DD4BF` at 0.3 fill, 0.6 stroke
- Walls: `#D9944A` at 0.3 fill, 0.6 stroke
- Material flow area: `#A78BFA` at 0.2 fill

#### Flow Animation
- Stage 1: Teal text particles enter from nozzle top
- Stage 2: Particles change to purple as they pass through grounding zone
- Stage 3: Purple liquid hits amber walls, constrained
- Stage 4: Clean output emerges at bottom, briefly glowing `#E2E8F0`

#### Stage Labels (along the right side)
- "intent" → "styled" → "constrained" → "code"
- Each label appears as the flow reaches that stage
- Colors match: `#2DD4BF` → `#A78BFA` → `#D9944A` → `#E2E8F0`

#### Bottom Statement
- "Prompt + Tests + Grounding." — Inter, 18px, bold, `#E2E8F0` at 0.7
- "Intent + Constraints + Style." — Inter, 16px, `#94A3B8` at 0.5
- "Together, they form a complete specification." — Inter, 14px, `#94A3B8` at 0.5

### Animation Sequence
1. **Frame 0-60 (0-2s):** Full mold visible with all regions glowing. Flow animation begins at nozzle.
2. **Frame 60-150 (2-5s):** Teal text particles flow into nozzle. "intent" label appears.
3. **Frame 150-240 (5-8s):** Particles transition to purple in grounding zone. "styled" label appears.
4. **Frame 240-300 (8-10s):** Purple liquid hits amber walls. "constrained" label appears.
5. **Frame 300-360 (10-12s):** Code output emerges. "code" label appears.
6. **Frame 360-420 (12-14s):** Bottom statement fades in. Hold — complete pipeline visible.

### Typography
- Stage labels: Inter, 14px, respective colors at 0.6
- Bottom line 1: Inter, 18px, bold (700), `#E2E8F0` at 0.7
- Bottom line 2: Inter, 16px, `#94A3B8` at 0.5
- Bottom line 3: Inter, 14px, `#94A3B8` at 0.5

### Easing
- Flow motion: `easeInOut(sine)` — organic
- Color transition: `easeInOut(cubic)` over 30 frames
- Wall contact: `easeOut(expo)` over 5 frames
- Labels: `easeOut(quad)` over 15 frames
- Statement: `easeOut(quad)` over 20 frames

## Narration Sync
> "Prompt plus tests plus grounding. Intent plus constraints plus style. Together, they form a complete specification."

Segment: `part3_mold_has_three_parts_026`

- **4:26** ("Prompt plus tests plus grounding"): Pipeline animation begins, all stages flowing
- **4:33** ("Intent plus constraints plus style"): Stage labels visible
- **4:37** ("complete specification"): Bottom statement, full pipeline visible

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Full mold — all regions */}
    <MoldOutline cx={960} cy={450} scale={1.3}
      nozzle={{ color: "#2DD4BF", fillOpacity: 0.3, strokeOpacity: 0.6 }}
      walls={{ color: "#D9944A", fillOpacity: 0.3, strokeOpacity: 0.6 }}
      material={{ color: "#A78BFA", fillOpacity: 0.2 }} />

    {/* Animated flow through pipeline */}
    <PipelineFlow
      stages={[
        { zone: "nozzle", color: "#2DD4BF", label: "intent" },
        { zone: "grounding", color: "#A78BFA", label: "styled" },
        { zone: "walls", color: "#D9944A", label: "constrained" },
        { zone: "output", color: "#E2E8F0", label: "code" }
      ]}
      stageDelay={60}
      flowDuration={420} />

    {/* Bottom statement */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="Prompt + Tests + Grounding."
          font="Inter" size={18} weight={700} color="#E2E8F0" opacity={0.7}
          x={960} y={860} align="center" />
        <Text text="Intent + Constraints + Style."
          font="Inter" size={16} color="#94A3B8" opacity={0.5}
          x={960} y={890} align="center" />
        <Text text="Together, they form a complete specification."
          font="Inter" size={14} color="#94A3B8" opacity={0.5}
          x={960} y={920} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "three_components_assembly",
  "pipeline": [
    { "stage": "prompt", "label": "intent", "color": "#2DD4BF" },
    { "stage": "grounding", "label": "styled", "color": "#A78BFA" },
    { "stage": "walls", "label": "constrained", "color": "#D9944A" },
    { "stage": "output", "label": "code", "color": "#E2E8F0" }
  ],
  "statement": "Prompt + Tests + Grounding. Intent + Constraints + Style.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_026"]
}
```

---
