[title:]

# Section 6.1: Where to Start — Section Title Card

**Tool:** Title
**Duration:** ~4s (120 frames @ 30fps)
**Timestamp:** 23:15 - 23:19

## Visual Description

A clean section title card for the final instructional section. "WHERE TO" appears first in large bold weight, then "START" fades in below with a slight offset-right. A thin horizontal rule draws between the two lines.

Behind the text, a faint ghost silhouette of a large codebase topology — interconnected nodes representing modules, files, and dependencies — sits at low opacity. The topology is dense and intimidating, hinting at the brownfield reality the section addresses. A single node near the edge pulses with a faint blue glow, suggesting the starting point. Background is deep navy-black.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Title Text
- "WHERE TO" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 460
- "START" — Inter, 72px, bold (700), `#E2E8F0`, centered at y: 545, offset-right 15px
- Horizontal rule: 200px wide, 2px, `#334155` at 0.5, centered between words at y: 505

#### Section Number
- "WHERE TO START" — Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px, centered at y: 400

#### Background Ghost (codebase topology)
- Network graph: 30-40 small circles (6px) connected by thin lines (1px)
- Spread across 800×500px area, centered
- Node color: `#94A3B8` at 0.03
- Edge color: `#94A3B8` at 0.015
- One node at edge position (1200, 600): `#4A90D9` at 0.06, with 12px Gaussian glow at `#4A90D9` at 0.03
- Pulsing: the glowing node breathes between 0.04 and 0.08 opacity

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Background fades in from black. Blueprint grid appears.
2. **Frame 15-40 (0.5-1.33s):** Section label fades in. Ghost codebase topology draws — nodes appear one by one (staggered), edges draw between them.
3. **Frame 40-60 (1.33-2s):** "WHERE TO" types on character-by-character (3 frames per character).
4. **Frame 60-70 (2-2.33s):** Horizontal rule draws from center outward.
5. **Frame 70-90 (2.33-3s):** "START" fades in with 10px upward slide.
6. **Frame 90-120 (3-4s):** Hold. The single glowing node pulses. Ghost topology fully drawn.

### Typography
- Section label: Inter, 14px, semi-bold (600), `#64748B` at 0.5, letter-spacing 4px
- Title words: Inter, 72px, bold (700), `#E2E8F0`
- Rule: `#334155` at 0.5

### Easing
- Text fade-in: `easeOut(quad)` over 20 frames
- "START" slide-up: `easeOut(cubic)` over 20 frames
- Rule draw: `easeInOut(quad)` over 10 frames
- Node stagger: `easeOut(quad)`, 1 frame per node
- Edge draw: `easeOut(cubic)` over 30 frames
- Node pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "Now — you don't work on a greenfield project. Nobody does."

Segment: `where_to_start_001`

- **0.0s** ("Now — you don't"): Title card begins fade-in
- **1.5s** ("work on a greenfield project"): "WHERE TO" typing on screen
- **3.0s** ("Nobody does."): "START" revealed, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Ghost codebase topology */}
    <Sequence from={15}>
      <NetworkGraph
        nodes={codebaseNodes} edges={codebaseEdges}
        nodeSize={6} nodeColor="#94A3B8" nodeOpacity={0.03}
        edgeColor="#94A3B8" edgeOpacity={0.015}
        staggerFrames={1} edgeDrawDuration={30}
        highlightNode={{
          index: 28, color: '#4A90D9', opacity: 0.06,
          glow: { blur: 12, opacity: 0.03 },
          pulse: { min: 0.04, max: 0.08, period: 40 }
        }}
      />
    </Sequence>

    {/* Section label */}
    <Sequence from={15}>
      <FadeIn duration={20}>
        <Text text="WHERE TO START" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.5}
          letterSpacing={4} x={960} y={400} align="center" />
      </FadeIn>
    </Sequence>

    {/* Title: WHERE TO */}
    <Sequence from={40}>
      <TypeWriter text="WHERE TO" font="Inter" size={72}
        weight={700} color="#E2E8F0"
        charDelay={3} x={960} y={460} align="center" />
    </Sequence>

    {/* Horizontal rule */}
    <Sequence from={60}>
      <DrawLine from={[860, 505]} to={[1060, 505]}
        color="#334155" opacity={0.5} width={2}
        drawDuration={10} fromCenter />
    </Sequence>

    {/* Title: START */}
    <Sequence from={70}>
      <SlideUp distance={10} duration={20}>
        <FadeIn duration={20}>
          <Text text="START" font="Inter" size={72}
            weight={700} color="#E2E8F0"
            x={975} y={545} align="center" />
        </FadeIn>
      </SlideUp>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "title_card",
  "sectionNumber": 6,
  "sectionLabel": "WHERE TO START",
  "titleLine1": "WHERE TO",
  "titleLine2": "START",
  "backgroundColor": "#0A0F1A",
  "ghostElements": [
    { "shape": "network_graph", "color": "#94A3B8", "component": "codebase_topology" },
    { "shape": "highlighted_node", "color": "#4A90D9", "component": "starting_point" }
  ],
  "narrationSegments": ["where_to_start_001"]
}
```

---
