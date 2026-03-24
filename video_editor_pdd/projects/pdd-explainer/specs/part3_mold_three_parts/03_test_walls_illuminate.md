[Remotion]

# Section 3.3: Test Walls Illuminate — Constraint Labels

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 0:53 - 1:03

## Visual Description

The mold cross-section is already on screen from the previous component. The camera focuses on the wall region. Each wall segment illuminates individually with a specific test-condition label:

- Wall 1: `null → None`
- Wall 2: `empty string → ''`
- Wall 3: `handles unicode`
- Wall 4: `latency < 100ms`
- Wall 5: `no exceptions thrown`
- Wall 6: `idempotent`

The labels appear in a monospace font as if they're test assertions. Each wall glows amber when its label appears. Animated liquid (representing code generation) begins flowing from the nozzle into the cavity — it flows freely until it contacts a wall, then stops cleanly against it. The shape of the liquid is defined entirely by the walls.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.08

### Chart/Visual Elements

#### Mold (persistent from 02)
- Same mold outline as 02, all regions visible but walls emphasized
- Walls stroke: `#D9944A` at 0.8 (brighter than other regions)

#### Wall Labels
- Font: JetBrains Mono, 12px, `#D9944A` at 0.8
- Each label positioned adjacent to its wall segment with a 1px connection line
- Labels stagger in from top to bottom

#### Liquid Flow
- Color: gradient from `#4A90D9` (cool blue) to `#A78BFA` (purple)
- Opacity: 0.3, with brighter leading edge at 0.6
- Flows downward from nozzle, spreads laterally
- Leading edge animates fluidly until contact with each wall
- On wall contact: brief `#D9944A` flash at 0.3 where liquid meets wall

### Animation Sequence
1. **Frame 0-30 (0-1s):** Camera zooms slightly into the wall region of the mold.
2. **Frame 30-60 (1-2s):** Wall 1 illuminates, label `null → None` appears.
3. **Frame 60-90 (2-3s):** Wall 2 illuminates, label `empty string → ''` appears.
4. **Frame 90-120 (3-4s):** Wall 3 illuminates, label `handles unicode` appears.
5. **Frame 120-150 (4-5s):** Walls 4-6 illuminate rapidly with remaining labels.
6. **Frame 150-240 (5-8s):** Liquid flows from nozzle into cavity. Hits walls, stops. Shape constrained.
7. **Frame 240-300 (8-10s):** Liquid fully fills cavity. Perfect shape defined by walls. Brief glow on all walls.

### Typography
- Wall labels: JetBrains Mono, 12px, `#D9944A` at 0.8
- "Each test is a constraint" subtitle: Inter, 14px, `#94A3B8` at 0.5, y: 920

### Easing
- Wall illuminate: `easeOut(cubic)` over 15 frames
- Label appear: `easeOut(quad)` over 10 frames
- Liquid flow: `easeInOut(sine)` — organic, fluid motion
- Wall contact flash: `easeOut(expo)` over 5 frames

## Narration Sync
> "First, tests. Tests are the walls of your mold."
> "Each test is a constraint. A boundary the generated code cannot cross."

Segments: `part3_mold_three_parts_007`, `part3_mold_three_parts_008`

- **0:59** ("First, tests"): Walls begin illuminating with labels
- **1:03** ("Each test is a constraint"): Liquid begins flowing, hitting walls

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.08} />
    <MoldOutline cx={960} cy={540} emphasize="walls" />

    {/* Wall labels stagger in */}
    {WALL_LABELS.map((wall, i) => (
      <Sequence from={30 + i * 30} key={wall.id}>
        <WallIlluminate
          wallId={wall.id} color="#D9944A"
          label={wall.label} font="JetBrains Mono"
          fontSize={12} illuminateDuration={15} />
      </Sequence>
    ))}

    {/* Liquid injection flow */}
    <Sequence from={150}>
      <LiquidFlow
        startY={300} endY={650}
        gradient={["#4A90D9", "#A78BFA"]}
        opacity={0.3} edgeOpacity={0.6}
        wallContactFlash="#D9944A"
        flowDuration={90} />
    </Sequence>

    {/* Subtitle */}
    <Sequence from={150}>
      <FadeIn duration={15}>
        <Text text="Each test is a constraint"
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
  "diagramId": "test_walls_illuminate",
  "walls": [
    { "id": "wall_null", "label": "null → None" },
    { "id": "wall_empty", "label": "empty string → ''" },
    { "id": "wall_unicode", "label": "handles unicode" },
    { "id": "wall_latency", "label": "latency < 100ms" },
    { "id": "wall_no_throw", "label": "no exceptions thrown" },
    { "id": "wall_idempotent", "label": "idempotent" }
  ],
  "wallColor": "#D9944A",
  "liquidGradient": ["#4A90D9", "#A78BFA"],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_007", "part3_mold_three_parts_008"]
}
```

---
