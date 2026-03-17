[Remotion]

# Section 6.3: Regenerate-Compare Loop — Circular Flow Diagram

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:31 - 23:39

## Visual Description

A circular flow diagram with three nodes connected by directional arrows forms the core PDD feedback loop. The three nodes are: **Prompt** (top center, blue), **Regenerate** (bottom-right, amber), and **Tests** (bottom-left, green). Arrows flow clockwise: Prompt → Regenerate → Tests → Prompt.

A golden traveling dot traces the circular path, completing one full cycle. As the dot passes through each node, the node illuminates and its label brightens. When the dot completes the cycle and returns to Prompt, the Prompt node transforms — it gains a golden outer ring and a "Source of Truth" badge floats up beneath it. The entire loop glows softly, communicating that this cycle is self-reinforcing: each iteration strengthens the prompt.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### Node Layout (equilateral triangle, centered at 960, 500)
- Triangle circumradius: 200px

#### Node — Prompt (top center)
- Position: (960, 320)
- Circle: 56px radius, `#4A90D9` at 0.15 fill, 3px `#4A90D9` at 0.6 stroke
- Icon: document glyph, 24px, `#4A90D9`
- Label: "Prompt" — Inter, 16px, semi-bold (600), `#4A90D9`, centered below at y=392

#### Node — Regenerate (bottom-right)
- Position: (1133, 620)
- Circle: 56px radius, `#D9944A` at 0.15 fill, 3px `#D9944A` at 0.6 stroke
- Icon: refresh/cycle glyph, 24px, `#D9944A`
- Label: "Regenerate" — Inter, 16px, semi-bold (600), `#D9944A`, centered below at y=692

#### Node — Tests (bottom-left)
- Position: (787, 620)
- Circle: 56px radius, `#5AAA6E` at 0.15 fill, 3px `#5AAA6E` at 0.6 stroke
- Icon: checkmark-in-shield glyph, 24px, `#5AAA6E`
- Label: "Tests" — Inter, 16px, semi-bold (600), `#5AAA6E`, centered below at y=692

#### Directional Arrows
- Arrow path: curved Bézier arcs connecting node edges, clockwise
- Arrow stroke: 2px, `#334155` at 0.5
- Arrowhead: 8px chevron at terminus
- Arrow 1: Prompt → Regenerate (right arc)
- Arrow 2: Regenerate → Tests (bottom arc)
- Arrow 3: Tests → Prompt (left arc)

#### Traveling Dot
- Diameter: 10px
- Color: `#FBBF24` (gold)
- Glow: 8px Gaussian blur, `#FBBF24` at 0.3
- Trail: 40px fading tail, `#FBBF24` at 0.1

#### Source of Truth Badge (appears at end)
- Position: (960, 400), below Prompt node
- Background: `#FBBF24` at 0.15, rounded 16px, 1px `#FBBF24` at 0.3 border
- Text: "Source of Truth" — Inter, 11px, semi-bold (600), `#FBBF24`
- Padding: 8px 16px

#### Prompt Node Golden Ring (appears at end)
- Outer ring: 66px radius, 3px `#FBBF24` at 0.6 stroke
- Glow: 14px Gaussian blur, `#FBBF24` at 0.15

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Three nodes fade in simultaneously with subtle scale pop. Labels appear. Arrows draw along their curved paths.
2. **Frame 40-70 (1.33-2.33s):** Golden dot spawns at Prompt node. Travels along Arrow 1 to Regenerate. Regenerate node illuminates (stroke brightens to 1.0, fill to 0.25).
3. **Frame 70-100 (2.33-3.33s):** Dot travels Arrow 2 to Tests. Tests node illuminates. Regenerate dims back to resting state.
4. **Frame 100-130 (3.33-4.33s):** Dot travels Arrow 3 back to Prompt. Prompt node illuminates. Tests dims back.
5. **Frame 130-170 (4.33-5.67s):** Prompt node transforms — golden outer ring draws in. Inner stroke transitions from blue to gold. "Source of Truth" badge slides up from below with fade.
6. **Frame 170-240 (5.67-8s):** Hold on complete diagram. All three nodes at resting brightness, Prompt has golden ring and badge. Subtle ambient pulse on the golden ring.

### Typography
- Node labels: Inter, 16px, semi-bold (600), respective node colors
- Badge text: Inter, 11px, semi-bold (600), `#FBBF24`

### Easing
- Node fade-in: `easeOut(back(1.2))` scale 0.8→1.0 over 20 frames
- Arrow draw: `easeInOut(cubic)` over 25 frames, staggered 5 frames each
- Dot travel: `easeInOut(quad)` per segment, 30 frames each
- Node illuminate: `easeOut(quad)` over 10 frames
- Golden ring draw: `easeOut(cubic)` over 20 frames
- Badge slide-up: `easeOut(cubic)` from y+20, 20 frames
- Ambient pulse: `easeInOut(sine)` opacity 0.15→0.25→0.15, looping 40 frames

## Narration Sync
> "When the regenerated version passes all tests, the prompt is your new source of truth for that module."

Segment: `where_to_start_001`

- **23:31** ("When the regenerated version"): Traveling dot begins its journey
- **23:34** ("passes all tests"): Dot reaches Tests node, which illuminates green
- **23:36** ("the prompt is your new source of truth"): Dot returns to Prompt, golden ring and badge appear
- **23:38** ("for that module"): Hold on complete diagram

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Three nodes */}
    <Sequence from={0}>
      <ScalePopIn from={0.8} to={1.0} duration={20}>
        <CircleNode x={960} y={320} radius={56}
          fill="#4A90D9" fillOpacity={0.15}
          stroke="#4A90D9" strokeOpacity={0.6} strokeWidth={3}
          icon="document" label="Prompt" />
        <CircleNode x={1133} y={620} radius={56}
          fill="#D9944A" fillOpacity={0.15}
          stroke="#D9944A" strokeOpacity={0.6} strokeWidth={3}
          icon="refresh" label="Regenerate" />
        <CircleNode x={787} y={620} radius={56}
          fill="#5AAA6E" fillOpacity={0.15}
          stroke="#5AAA6E" strokeOpacity={0.6} strokeWidth={3}
          icon="shield_check" label="Tests" />
      </ScalePopIn>
    </Sequence>

    {/* Directional arrows */}
    <Sequence from={15}>
      <CurvedArrow from={[960, 320]} to={[1133, 620]}
        color="#334155" opacity={0.5} width={2}
        arrowSize={8} drawDuration={25} />
      <Sequence from={5}>
        <CurvedArrow from={[1133, 620]} to={[787, 620]}
          color="#334155" opacity={0.5} width={2}
          arrowSize={8} drawDuration={25} />
      </Sequence>
      <Sequence from={10}>
        <CurvedArrow from={[787, 620]} to={[960, 320]}
          color="#334155" opacity={0.5} width={2}
          arrowSize={8} drawDuration={25} />
      </Sequence>
    </Sequence>

    {/* Traveling golden dot */}
    <Sequence from={40}>
      <TravelingDot
        path={[
          { node: [960, 320], arc: 'right' },
          { node: [1133, 620], arc: 'bottom' },
          { node: [787, 620], arc: 'left' },
          { node: [960, 320] }
        ]}
        color="#FBBF24" size={10} glowBlur={8}
        trailLength={40} segmentDuration={30}
        onPass={(nodeIndex) => illuminateNode(nodeIndex)}
      />
    </Sequence>

    {/* Golden ring + Source of Truth badge */}
    <Sequence from={130}>
      <StrokeDraw duration={20}>
        <Circle x={960} y={320} radius={66}
          stroke="#FBBF24" strokeOpacity={0.6} strokeWidth={3}
          glow={{ blur: 14, color: '#FBBF24', opacity: 0.15 }} />
      </StrokeDraw>
      <Sequence from={10}>
        <SlideIn direction="up" distance={20} duration={20}>
          <Badge x={960} y={400} text="Source of Truth"
            bgColor="#FBBF24" bgOpacity={0.15}
            borderColor="#FBBF24" borderOpacity={0.3}
            textColor="#FBBF24" font="Inter" size={11}
            weight={600} />
        </SlideIn>
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "flow_diagram",
  "diagramId": "regenerate_compare_loop",
  "nodes": [
    {
      "id": "prompt",
      "label": "Prompt",
      "color": "#4A90D9",
      "position": [960, 320],
      "icon": "document"
    },
    {
      "id": "regenerate",
      "label": "Regenerate",
      "color": "#D9944A",
      "position": [1133, 620],
      "icon": "refresh"
    },
    {
      "id": "tests",
      "label": "Tests",
      "color": "#5AAA6E",
      "position": [787, 620],
      "icon": "shield_check"
    }
  ],
  "flow": "clockwise",
  "travelingDotColor": "#FBBF24",
  "badge": {
    "text": "Source of Truth",
    "attachedTo": "prompt"
  },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_001"]
}
```

---
