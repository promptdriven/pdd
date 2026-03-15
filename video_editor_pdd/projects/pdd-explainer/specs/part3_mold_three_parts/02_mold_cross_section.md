[Remotion]

# Section 3.2: Mold Cross-Section — Three Components Reveal

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 13:04 - 13:19

## Visual Description
A technical cross-section of an injection mold fills the screen. The mold is drawn as a clean, geometric cutaway — a rectangular cavity with defined walls, a nozzle at the top, and a material flow channel. Three regions highlight sequentially: the **walls** (tests, amber), the **nozzle/inlet** (prompt, blue), and the **material flowing through** (grounding, green). Each region illuminates with its label as the narrator introduces the concept. Liquid (representing code) then injects through the nozzle, fills the cavity, and is constrained by the walls — a visual preview of how the three components work together.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Faint blueprint grid `rgba(255,255,255,0.03)`, 40px spacing

### Chart/Visual Elements
- **Mold Body:** Centered, 800px wide x 500px tall, outer shell in `#334155` with 2px stroke `#475569`, rounded corners 4px
- **Cavity:** Inner negative space, 600px wide x 300px tall, centered within mold body, dark background showing through
- **Wall Segments (Tests):** Left wall, right wall, and bottom wall of the cavity — each 20px thick, initially `#475569`, highlight color `#D9944A` at 0.6 opacity
  - Wall labels (appearing on highlight): "null → None", "empty string → ''", "handles unicode", "latency < 100ms" — each 12px, `#D9944A`, positioned along respective walls
- **Nozzle (Prompt):** Funnel shape at top-center of cavity, 80px wide at top tapering to 30px, fill `#4A90D9` at 0.4 opacity
  - Label: "intent", "requirements", "constraints" stacked vertically inside nozzle, 12px, `#4A90D9`
- **Material Channel (Grounding):** Subtle texture fill behind the liquid flow, `#5AAA6E` at 0.15 opacity, visible as a tint on the flowing liquid
- **Liquid Flow:** Animated particles/fluid flowing from nozzle downward, filling cavity. Blue-tinted `rgba(74,144,217,0.5)` with slight green tint from grounding `rgba(90,170,110,0.2)`
- **Section Label (top-left):** "Three types of capital" — `#FFFFFF` at 0.6 opacity, 20px

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Mold body draws in — outer shell, then cavity negative space, blueprint grid visible
2. **Frame 40-100 (1.33-3.33s):** Wall segments highlight amber one by one (left, bottom, right). Each wall glows `#D9944A` at 0.6 opacity. Individual constraint labels fade in along each wall with 10-frame stagger
3. **Frame 100-160 (3.33-5.33s):** Nozzle region highlights blue. "intent", "requirements", "constraints" labels fade in inside the nozzle funnel
4. **Frame 160-220 (5.33-7.33s):** Material channel tints green. Subtle texture/pattern appears behind the cavity space
5. **Frame 220-350 (7.33-11.67s):** Liquid injection animation — fluid particles stream from nozzle, flow downward, spread laterally, fill cavity progressively. Liquid respects wall boundaries (stops at edges). Fill level rises from 0% to 100%
6. **Frame 350-400 (11.67-13.33s):** Liquid settles. Surface smooths. A clean "code block" shape emerges from the filled mold — the output
7. **Frame 400-450 (13.33-15.0s):** Hold. All three regions glow at their respective colors. The output glows faintly then dims — the mold stays bright

### Typography
- Section Label: Inter, 20px, regular (400), `#FFFFFF`, opacity 0.6
- Wall Labels: JetBrains Mono, 12px, regular (400), `#D9944A`
- Nozzle Labels: Inter, 12px, semi-bold (600), `#4A90D9`
- Component Names (appearing next to regions): Inter, 24px, bold (700), respective color at 0.8 opacity

### Easing
- Mold body draw: `easeOut(cubic)`
- Wall highlights: `easeInOut(sine)`
- Label fades: `easeOut(quad)`
- Liquid flow: `easeIn(quad)` for initial stream, `easeOut(cubic)` for fill spread
- Output emerge: `easeOut(quad)`

## Narration Sync
> "In PDD, the mold has three components. Three types of capital you're accumulating."
> "First: tests. Tests are the walls of your mold."
> "Each test is a constraint. A boundary the generated code cannot cross."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Mold Body */}
  <Sequence from={0} durationInFrames={40}>
    <MoldBody width={800} height={500} cavityWidth={600} cavityHeight={300} />
  </Sequence>

  {/* Wall Highlights (Tests) */}
  <Sequence from={40} durationInFrames={60}>
    <WallHighlight
      walls={["left", "bottom", "right"]}
      color="#D9944A"
      labels={["null → None", "empty string → ''", "handles unicode", "latency < 100ms"]}
      stagger={10}
    />
  </Sequence>

  {/* Nozzle Highlight (Prompt) */}
  <Sequence from={100} durationInFrames={60}>
    <NozzleHighlight
      color="#4A90D9"
      labels={["intent", "requirements", "constraints"]}
    />
  </Sequence>

  {/* Material Channel (Grounding) */}
  <Sequence from={160} durationInFrames={60}>
    <MaterialChannel color="#5AAA6E" />
  </Sequence>

  {/* Liquid Injection */}
  <Sequence from={220} durationInFrames={130}>
    <LiquidFill
      fromNozzle={true}
      fillColor="rgba(74,144,217,0.5)"
      groundingTint="rgba(90,170,110,0.2)"
      respectWalls={true}
    />
  </Sequence>

  {/* Output Emerge */}
  <Sequence from={350} durationInFrames={50}>
    <CodeOutput glow={true} fadeGlow={true} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "mold": {
    "outerWidth": 800,
    "outerHeight": 500,
    "cavityWidth": 600,
    "cavityHeight": 300,
    "shellColor": "#334155",
    "strokeColor": "#475569"
  },
  "walls": {
    "thickness": 20,
    "highlightColor": "#D9944A",
    "highlightOpacity": 0.6,
    "labels": ["null → None", "empty string → ''", "handles unicode", "latency < 100ms"]
  },
  "nozzle": {
    "topWidth": 80,
    "bottomWidth": 30,
    "color": "#4A90D9",
    "opacity": 0.4,
    "labels": ["intent", "requirements", "constraints"]
  },
  "grounding": {
    "color": "#5AAA6E",
    "opacity": 0.15
  },
  "liquid": {
    "primaryColor": "rgba(74,144,217,0.5)",
    "groundingTint": "rgba(90,170,110,0.2)"
  }
}
```

---
