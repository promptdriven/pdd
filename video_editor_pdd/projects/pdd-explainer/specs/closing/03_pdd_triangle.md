[Remotion]

# Section 7.3: PDD Triangle — Prompt, Tests, Grounding

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 24:33 - 24:43

## Visual Description
The three core components of PDD materialize as a triangle diagram — the video's definitive visual thesis. PROMPT sits at the apex in cool blue, TESTS at bottom-left in warm amber, GROUNDING at bottom-right in soft green. Each vertex is a rounded node connected by subtle glowing edges. As the narrator names each component, that vertex illuminates and its label appears. Once all three are lit, the center of the triangle fills with generated code — simplified horizontal bars rendered in neutral gray. The triangle represents the "mold" that shapes the disposable code. The animation is deliberate and rhythmic, matching the narrator's measured cadence: one component per beat.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy), with a very subtle radial gradient center — `#111D2E` at the triangle's centroid fading to `#0F172A` at edges
- Grid lines: None

### Chart/Visual Elements
- **Triangle Edges:** Three lines connecting vertices, `rgba(255,255,255,0.08)` initially, brightening to `rgba(255,255,255,0.15)` once all vertices are lit. Stroke 1.5px. Vertices at:
  - Top: (960, 240)
  - Bottom-left: (520, 720)
  - Bottom-right: (1400, 720)
- **PROMPT Node (Top):**
  - Circle: 60px diameter, `#4A90D9` at 0.15 opacity fill, `#4A90D9` at 0.6 opacity stroke (2px), centered at (960, 240)
  - Icon: Simplified document/pencil icon inside, `#4A90D9` at 0.5 opacity, 24px
  - Label: "PROMPT" — `#4A90D9`, 18px Inter semi-bold, positioned at (960, 180), centered
  - Subtitle: "Encodes intent" — `#4A90D9` at 0.4 opacity, 14px Inter regular, positioned at (960, 310)
- **TESTS Node (Bottom-left):**
  - Circle: 60px diameter, `#D9944A` at 0.15 opacity fill, `#D9944A` at 0.6 opacity stroke (2px), centered at (520, 720)
  - Icon: Simplified checkmark/shield icon, `#D9944A` at 0.5 opacity, 24px
  - Label: "TESTS" — `#D9944A`, 18px Inter semi-bold, positioned at (520, 790), centered
  - Subtitle: "Preserve behavior" — `#D9944A` at 0.4 opacity, 14px Inter regular, positioned at (520, 660)
- **GROUNDING Node (Bottom-right):**
  - Circle: 60px diameter, `#5AAA6E` at 0.15 opacity fill, `#5AAA6E` at 0.6 opacity stroke (2px), centered at (1400, 720)
  - Icon: Simplified anchor/pin icon, `#5AAA6E` at 0.5 opacity, 24px
  - Label: "GROUNDING" — `#5AAA6E`, 18px Inter semi-bold, positioned at (1400, 790), centered
  - Subtitle: "Maintains style" — `#5AAA6E` at 0.4 opacity, 14px Inter regular, positioned at (1400, 660)
- **Generated Code (Center):**
  - Cluster of 8 horizontal bars (simulated code lines), varying widths (60-200px), `rgba(255,255,255,0.12)`, height 6px, spaced 16px apart, centered at triangle centroid (960, 560)
  - Very subtle multi-color tint: top bars lean slightly blue, left bars slightly amber, right bars slightly green — representing influence from each vertex
- **Directional Arrows:** Three small chevrons (›) along each edge, pointing inward toward center, `rgba(255,255,255,0.06)`, appearing after code materializes — showing that the mold shapes the code

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Triangle edges draw on simultaneously — three lines grow from vertices toward each other, meeting at midpoints. Edges start at `rgba(255,255,255,0.04)` and reach `rgba(255,255,255,0.08)`
2. **Frame 30-80 (1.0-2.67s):** PROMPT node illuminates — circle scales 0.8→1.0 with fill opacity 0→0.15, stroke brightens. Label "PROMPT" fades in above. Subtitle "Encodes intent" fades in below. Synced with narrator saying "Prompts encode intent."
3. **Frame 80-130 (2.67-4.33s):** TESTS node illuminates — same animation pattern. Label "TESTS" and subtitle "Preserve behavior" fade in. Synced with "Tests preserve behavior." Edge from PROMPT to TESTS brightens
4. **Frame 130-180 (4.33-6.0s):** GROUNDING node illuminates. Label "GROUNDING" and subtitle "Maintains style" fade in. Synced with "Grounding maintains style." All edges now at full brightness `rgba(255,255,255,0.15)`
5. **Frame 180-210 (6.0-7.0s):** Radial gradient background intensifies slightly at center. Generated code bars appear one by one from center outward (3-frame stagger per bar)
6. **Frame 210-240 (7.0-8.0s):** Directional arrows fade in along edges, pointing inward. Code bars pulse once with a subtle multi-color tint
7. **Frame 240-300 (8.0-10.0s):** Hold at final state. All three nodes breathe gently (0.02 opacity oscillation on fills, staggered phase). Code bars have very slow ambient shimmer

### Typography
- Node Labels: Inter, 18px, semi-bold (600), color matches respective node
- Node Subtitles: Inter, 14px, regular (400), color matches node at 0.4 opacity
- Letter-spacing on labels: 2px

### Easing
- Edge draw: `easeOut(cubic)`
- Node illuminate/scale: `easeOut(quad)`
- Label fade-in: `easeOut(quad)`
- Code bar stagger: `easeOut(cubic)`
- Arrow fade: `easeOut(quad)`
- Ambient breathing: `easeInOut(sine)`

## Narration Sync
> "Prompts encode intent. Tests preserve behavior. Grounding maintains style."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Radial gradient background */}
    <RadialGradient center={[960, 560]} color="#111D2E" />

    {/* Triangle Edges */}
    <Sequence from={0} durationInFrames={30}>
      <TriangleEdges
        vertices={[[960, 240], [520, 720], [1400, 720]]}
        strokeWidth={1.5}
        initialOpacity={0.04}
        finalOpacity={0.08}
      />
    </Sequence>

    {/* PROMPT Node */}
    <Sequence from={30} durationInFrames={50}>
      <TriangleNode
        x={960} y={240}
        label="PROMPT"
        subtitle="Encodes intent"
        color="#4A90D9"
        icon="document"
      />
    </Sequence>

    {/* TESTS Node */}
    <Sequence from={80} durationInFrames={50}>
      <TriangleNode
        x={520} y={720}
        label="TESTS"
        subtitle="Preserve behavior"
        color="#D9944A"
        icon="checkmark"
      />
    </Sequence>

    {/* GROUNDING Node */}
    <Sequence from={130} durationInFrames={50}>
      <TriangleNode
        x={1400} y={720}
        label="GROUNDING"
        subtitle="Maintains style"
        color="#5AAA6E"
        icon="anchor"
      />
    </Sequence>

    {/* Edge brightness boost after all nodes lit */}
    <Sequence from={170} durationInFrames={10}>
      <TriangleEdgeBrighten finalOpacity={0.15} />
    </Sequence>

    {/* Generated Code Center */}
    <Sequence from={180} durationInFrames={30}>
      <GeneratedCodeBars
        count={8}
        center={[960, 560]}
        stagger={3}
        barHeight={6}
      />
    </Sequence>

    {/* Directional Arrows */}
    <Sequence from={210} durationInFrames={30}>
      <DirectionalArrows
        vertices={[[960, 240], [520, 720], [1400, 720]]}
        target={[960, 560]}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "gradientCenter": "#111D2E",
  "triangle": {
    "vertices": {
      "top": [960, 240],
      "bottomLeft": [520, 720],
      "bottomRight": [1400, 720]
    },
    "centroid": [960, 560],
    "edgeStroke": 1.5
  },
  "nodes": [
    {
      "label": "PROMPT",
      "subtitle": "Encodes intent",
      "position": [960, 240],
      "color": "#4A90D9",
      "icon": "document",
      "radius": 30
    },
    {
      "label": "TESTS",
      "subtitle": "Preserve behavior",
      "position": [520, 720],
      "color": "#D9944A",
      "icon": "checkmark",
      "radius": 30
    },
    {
      "label": "GROUNDING",
      "subtitle": "Maintains style",
      "position": [1400, 720],
      "color": "#5AAA6E",
      "icon": "anchor",
      "radius": 30
    }
  ],
  "generatedCode": {
    "bars": 8,
    "barHeight": 6,
    "spacing": 16,
    "color": "rgba(255,255,255,0.12)"
  }
}
```

---
