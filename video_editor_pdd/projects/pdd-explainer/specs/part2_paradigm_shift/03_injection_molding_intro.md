[Remotion]

# Section 2.3: Injection Molding Intro — Craft to Mold

**Tool:** Remotion
**Duration:** ~15s (450 frames @ 30fps)
**Timestamp:** 8:52 - 9:07

## Visual Description
An animated diagram introduces the injection molding metaphor. The screen begins with a single hand-crafted object (a stylized chair wireframe) on the left side, labeled "Crafting." A transformation sequence plays: the chair dissolves into particles that reform on the right side as a rectangular mold cavity cross-section. Liquid pours into the mold, solidifies, and a finished part ejects — identical to the original chair shape. Then the mold produces a SECOND identical part, then a THIRD, with each ejecting faster. A counter in the corner tallies "Parts: 1… 2… 3…" Below the mold, a callout reads: "Refine the mold once → every future part improves." The visual drives home that value migrated from the individual object to the reusable specification.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: None

### Chart/Visual Elements
- **Crafted Object (Left Phase)**
  - Position: centered at (480, 440)
  - Wireframe chair: 120px x 160px, stroke `#4A90D9`, 2px, 4 leg lines + seat rectangle + back rectangle
  - Label: "Crafting" — `#94A3B8`, 20px, below at Y=560
- **Mold Cavity (Right Phase)**
  - Position: centered at (960, 400)
  - Cross-section: 300px wide x 200px tall, wall thickness 20px
  - Outer walls: `#D9944A` at 0.6 opacity, filled rectangles
  - Inner cavity: negative space matching chair profile
  - Inlet funnel: top-center, 50px wide, `#475569`
  - Label: "Molding" — `#94A3B8`, 20px, positioned at (960, 560)
- **Liquid Fill:** Animated particles/blob, `rgba(74,144,217,0.5)`, filling cavity from top
- **Ejected Parts:** Solid chair silhouettes, `#4A90D9` at 0.7 opacity, 60px tall, stacking to the right of the mold at X=1300, 1380, 1460
- **Parts Counter:** Top-right corner (1700, 80), "Parts: N" — `#FFFFFF` at 0.7, 22px
- **Callout:** Bottom-center at Y=780, rounded rect 700px x 70px, border `rgba(217,148,74,0.3)`, text "Refine the mold once → every future part improves" — `#CBD5E1`, 18px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Crafted chair wireframe draws in stroke-by-stroke on the left. "Crafting" label fades in
2. **Frame 30-60 (1-2s):** Hold on crafted chair
3. **Frame 60-120 (2-4s):** Chair dissolves into ~40 particles that drift rightward and reform as the mold cavity outline. "Crafting" label fades out, "Molding" label fades in
4. **Frame 120-180 (4-6s):** Liquid pours from inlet, fills cavity, solidifies (color shifts from `rgba(74,144,217,0.5)` to `rgba(74,144,217,0.8)`). First part ejects rightward to X=1300. Counter: "Parts: 1"
5. **Frame 180-220 (6-7.3s):** Second fill-and-eject cycle, faster (40 frames vs 60). Part appears at X=1380. Counter: "Parts: 2"
6. **Frame 220-250 (7.3-8.3s):** Third fill-and-eject cycle, even faster (30 frames). Part at X=1460. Counter: "Parts: 3"
7. **Frame 250-310 (8.3-10.3s):** Counter pulses. Mold outline glows briefly (`#D9944A` at 0.9). A wrench icon appears near the mold, taps once, glow ripple indicates "refinement"
8. **Frame 310-370 (10.3-12.3s):** All three ejected parts simultaneously glow brighter (0.7→0.9 opacity) to show improvement propagating. Callout slides up and fades in
9. **Frame 370-450 (12.3-15s):** Hold at final state

### Typography
- Phase Labels: Inter, 20px, semi-bold (600), `#94A3B8`
- Parts Counter: Inter, 22px, bold (700), `#FFFFFF` at 0.7 opacity
- Callout Text: Inter, 18px, regular (400), `#CBD5E1`

### Easing
- Wireframe draw: `easeOut(cubic)`
- Particle dissolve/reform: `easeInOut(cubic)` with staggered delay per particle
- Liquid fill: `easeOut(quad)`
- Part eject: `easeOut(back(1.2))`
- Counter increment: `easeOut(quad)`
- Mold glow pulse: `easeInOut(sine)`
- Callout slide: `easeOut(cubic)`

## Narration Sync
> "There's a pattern here that shows up across industries. Not just cheaper materials, a deeper shift in how things are made."
> "Consider injection molding. Before it existed, you crafted individual objects. After it? You designed molds."
> "Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={450}>
  {/* Phase 1: Crafted Object */}
  <Sequence from={0} durationInFrames={60}>
    <WireframeChair x={480} y={440} width={120} height={160} color="#4A90D9" />
    <PhaseLabel text="Crafting" x={480} y={560} />
  </Sequence>

  {/* Particle Transition */}
  <Sequence from={60} durationInFrames={60}>
    <ParticleDissolveReform
      fromShape="chair" toShape="moldCavity"
      fromPos={{ x: 480, y: 440 }} toPos={{ x: 960, y: 400 }}
      particleCount={40}
    />
  </Sequence>

  {/* Phase 2: Mold Operation */}
  <Sequence from={120} durationInFrames={130}>
    <MoldCavity x={960} y={400} width={300} height={200} wallColor="#D9944A" />
    <PhaseLabel text="Molding" x={960} y={560} />
    <LiquidFillEjectCycle
      cycles={3}
      ejectPositions={[1300, 1380, 1460]}
      fillColor="rgba(74,144,217,0.5)"
      partColor="#4A90D9"
    />
    <PartsCounter x={1700} y={80} />
  </Sequence>

  {/* Refinement Beat */}
  <Sequence from={250} durationInFrames={60}>
    <WrenchRefinement moldX={960} moldY={400} glowColor="#D9944A" />
  </Sequence>

  {/* Improvement Propagation + Callout */}
  <Sequence from={310} durationInFrames={60}>
    <PartGlowPropagation positions={[1300, 1380, 1460]} />
    <CalloutCard
      y={780} width={700}
      text="Refine the mold once → every future part improves"
      borderColor="rgba(217,148,74,0.3)"
    />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "craftedObject": {
    "type": "wireframeChair",
    "position": { "x": 480, "y": 440 },
    "size": { "width": 120, "height": 160 },
    "color": "#4A90D9"
  },
  "mold": {
    "position": { "x": 960, "y": 400 },
    "cavityWidth": 300,
    "cavityHeight": 200,
    "wallThickness": 20,
    "wallColor": "#D9944A",
    "inletWidth": 50,
    "inletColor": "#475569"
  },
  "liquidFill": {
    "color": "rgba(74,144,217,0.5)",
    "solidifiedColor": "rgba(74,144,217,0.8)"
  },
  "ejectedParts": {
    "positions": [1300, 1380, 1460],
    "color": "#4A90D9",
    "size": 60
  },
  "callout": {
    "text": "Refine the mold once → every future part improves",
    "borderColor": "rgba(217,148,74,0.3)"
  }
}
```

---
