[Remotion]

# Section 4.4: Injection Mold — Walls Do the Precision Work

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 18:52 - 19:00

## Visual Description
A full-screen close-up of the injection mold metaphor. A clean, geometric mold cavity sits at center — thick amber walls forming a precise shape. Liquid pours from a nozzle at the top and flows freely downward in a chaotic, organic motion. As the liquid contacts each wall, the wall brightens and a constraint label appears on it (e.g., "handles null", "returns list", "< 100ms"). The liquid is messy and imprecise, but the final filled shape is perfectly clean — the walls did all the precision work. A small label at top-left reads: "Precision comes from constraints, not specification." The result is the same shape as the 3D printer was trying to deposit point-by-point, but achieved through containment rather than explicit placement.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` (solid fill)
- Grid lines: Faint blueprint grid `rgba(255,255,255,0.03)`, 40px spacing

### Chart/Visual Elements
- **Mold Cavity:** Centered at (960, 540), total outer bound 700px wide x 440px tall, inner cavity shaped as a curly brace (matching the 3D printer shape), wall thickness 20px, wall color `#D9944A` at 0.4 opacity initially
- **Nozzle Inlet:** Top-center, funnel shape 60px wide tapering to 24px, `#475569`, positioned at top of cavity
- **Liquid:** Animated fluid particles, `rgba(74,144,217,0.45)`, chaotic/organic motion — splashes, pools, spreads irregularly. Each particle is a small circle (3-6px) moving with slight randomness
- **Wall Constraint Labels:** 6 labels placed along the cavity walls, each appearing when liquid first contacts that wall segment:
  - Left wall: "handles null", "empty string → ''"
  - Bottom wall: "returns sorted list"
  - Right wall: "latency < 100ms", "valid JSON output"
  - Top-right corner: "no side effects"
  - Each label: JetBrains Mono 12px, `#D9944A` at 0.7 opacity
- **Wall Glow on Contact:** When liquid touches a wall segment, that segment brightens from 0.4 → 0.8 opacity for 15 frames, then settles at 0.6
- **Section Label (top-left):** "Precision from constraints, not specification" — Inter 18px, `#94A3B8` at 0.5 opacity, positioned at (60, 40)
- **Final Shape Outline:** After fill completes, a clean white stroke (`#FFFFFF` at 0.3, 1px) traces the inner shape — the same curly brace as in the 3D printer spec

### Animation Sequence
1. **Frame 0-30 (0-1.0s):** Mold cavity walls draw in (stroke-dashoffset reveal). Blueprint grid visible. Section label fades in
2. **Frame 30-60 (1.0-2.0s):** Nozzle fades in. First liquid particles begin dropping from inlet — organic, gravity-driven motion with slight horizontal randomness
3. **Frame 60-120 (2.0-4.0s):** Liquid pool grows at the bottom of cavity. Contacts bottom wall first — wall pulses, "returns sorted list" label appears. Liquid spreads left — left wall contact, "handles null" label appears. Spreads right — right wall contact, "latency < 100ms" label appears
4. **Frame 120-170 (4.0-5.67s):** Liquid continues filling. More wall contacts trigger remaining labels. Each contact: wall glows, label fades in with 8px outward drift from wall
5. **Frame 170-210 (5.67-7.0s):** Cavity fully filled. Liquid surface settles, smooths. The chaotic particles merge into a clean, solid fill — `rgba(74,144,217,0.35)`
6. **Frame 210-240 (7.0-8.0s):** Hold. Clean white outline traces the final shape. All 6 constraint labels visible. Walls glow at settled 0.6 opacity. The shape is identical to the 3D printer target — achieved through constraints, not specification

### Typography
- Section Label: Inter, 18px, regular (400), `#94A3B8` at 0.5 opacity
- Constraint Labels: JetBrains Mono, 12px, regular (400), `#D9944A` at 0.7 opacity

### Easing
- Wall draw-in: `easeInOut(cubic)`
- Liquid particle drop: `easeIn(quad)` (gravity)
- Liquid lateral spread: `easeOut(cubic)`
- Wall glow pulse: `easeInOut(sine)`
- Label appear/drift: `easeOut(quad)`
- Surface settle: `easeOut(cubic)`
- Shape outline trace: `easeInOut(quad)`

## Narration Sync
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  {/* Mold Cavity Walls */}
  <Sequence from={0} durationInFrames={30}>
    <MoldCavity
      shape="curlyBrace"
      width={700}
      height={440}
      wallThickness={20}
      wallColor="#D9944A"
      initialOpacity={0.4}
    />
  </Sequence>

  {/* Section Label */}
  <Sequence from={0} durationInFrames={30}>
    <FadeIn>
      <Label text="Precision from constraints, not specification" x={60} y={40} />
    </FadeIn>
  </Sequence>

  {/* Nozzle */}
  <Sequence from={30} durationInFrames={15}>
    <FadeIn>
      <Nozzle width={60} taperWidth={24} color="#475569" />
    </FadeIn>
  </Sequence>

  {/* Liquid Pour with Wall Contacts */}
  <Sequence from={45} durationInFrames={165}>
    <LiquidSimulation
      particleColor="rgba(74,144,217,0.45)"
      particleSize={[3, 6]}
      gravity={0.4}
      horizontalRandomness={0.2}
      wallContacts={wallContactEvents}
      wallGlowColor="#D9944A"
      wallGlowPeakOpacity={0.8}
      wallGlowSettleOpacity={0.6}
    />
  </Sequence>

  {/* Constraint Labels (triggered by wall contacts) */}
  <Sequence from={60} durationInFrames={110}>
    <ConstraintLabels
      labels={constraintData}
      font="JetBrains Mono"
      fontSize={12}
      color="#D9944A"
      driftDistance={8}
    />
  </Sequence>

  {/* Final Shape Outline */}
  <Sequence from={210} durationInFrames={30}>
    <ShapeOutline shape="curlyBrace" strokeColor="#FFFFFF" strokeOpacity={0.3} />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "cavity": {
    "shape": "curlyBrace",
    "width": 700,
    "height": 440,
    "wallThickness": 20,
    "wallColor": "#D9944A",
    "initialOpacity": 0.4,
    "contactOpacity": 0.8,
    "settledOpacity": 0.6
  },
  "nozzle": {
    "topWidth": 60,
    "bottomWidth": 24,
    "color": "#475569"
  },
  "liquid": {
    "particleColor": "rgba(74,144,217,0.45)",
    "particleSizeRange": [3, 6],
    "settledFillColor": "rgba(74,144,217,0.35)"
  },
  "constraintLabels": [
    { "text": "handles null", "wall": "left", "position": 0.3, "triggerFrame": 80 },
    { "text": "empty string → ''", "wall": "left", "position": 0.7, "triggerFrame": 95 },
    { "text": "returns sorted list", "wall": "bottom", "position": 0.5, "triggerFrame": 70 },
    { "text": "latency < 100ms", "wall": "right", "position": 0.3, "triggerFrame": 90 },
    { "text": "valid JSON output", "wall": "right", "position": 0.7, "triggerFrame": 110 },
    { "text": "no side effects", "wall": "top-right", "position": 0.8, "triggerFrame": 130 }
  ]
}
```

---
