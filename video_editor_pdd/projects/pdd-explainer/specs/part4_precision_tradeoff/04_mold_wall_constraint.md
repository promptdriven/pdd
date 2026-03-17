[Remotion]

# Section 4.4: Mold Wall Constraint — Precision from Boundaries

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 18:58 - 19:08

## Visual Description

A focused close-up on the injection molding paradigm. A large mold cavity occupies the center of the screen. Liquid material enters from a nozzle at the top and flows chaotically inside — swirling, splashing, bouncing off walls. The liquid's path is deliberately random and messy. But as it fills the cavity and settles, the final shape is perfect — the walls did all the precision work.

The key visual beat: each wall segment of the mold lights up individually with a label — "Wall 1: input validation", "Wall 2: error format", "Wall 3: edge case null", "Wall 4: return type" — mapping walls to test constraints. This makes the metaphor explicit: tests are walls, and walls provide precision without requiring the "liquid" (LLM-generated code) to follow any particular path.

A small counter shows "Constraints defined: 4" versus the implied thousands of behavioral points those 4 walls constrain.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (near-black navy)
- Subtle radial gradient from center, `#0F172A` at 0.15

### Chart/Visual Elements

#### Mold Cavity
- Large cross-section centered at (960, 480), ~500x550px
- Shape: bracket-like form matching the shape from 03_coordinate_grid_precision
- Walls: `#D9944A` at 0.4, 4px stroke initially
- Cavity interior: `#0F172A` at 0.1
- Nozzle gate: opening at top center, 30px wide

#### Wall Segments (labeled individually)
- Wall 1 (top): highlighted segment, `#D9944A` at 0.7 when active
  - Label: "input validation" — JetBrains Mono, 10px, `#D9944A` at 0.6
  - Leader line from wall to label, 1px dashed
- Wall 2 (right): highlighted segment, `#D9944A` at 0.7
  - Label: "error format"
- Wall 3 (bottom): highlighted segment, `#D9944A` at 0.7
  - Label: "edge case: null"
- Wall 4 (left): highlighted segment, `#D9944A` at 0.7
  - Label: "return type"

#### Flowing Liquid
- 60-80 circular particles, sizes 5-12px, `#94A3B8` at 0.3
- Enter from nozzle gate with downward velocity + random lateral scatter
- Physics: gravity (0.3px/frame²), wall collision (bounce, damping 0.85)
- As liquid settles: particles merge into a solid fill, `#94A3B8` at 0.2, matching cavity shape

#### Constraint Counter
- "Constraints defined: 4" — JetBrains Mono, 16px, `#D9944A` at 0.7, at (960, 920)
- "Behaviors constrained: ∞" — JetBrains Mono, 12px, `#64748B` at 0.4, at (960, 950)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold cavity draws itself — walls appear segment by segment, each with a subtle amber flash.
2. **Frame 30-50 (1-1.67s):** Nozzle gate opens. First liquid particles enter from top.
3. **Frame 50-150 (1.67-5s):** Liquid flows chaotically — particles bounce off walls, swirl, splash. The motion is deliberately messy and organic. Particles accumulate at the bottom, gradually filling the cavity.
4. **Frame 150-200 (5-6.67s):** Liquid has filled the cavity. Particles merge into solid fill. The shape is perfect despite the chaotic filling process. Walls begin glowing.
5. **Frame 200-260 (6.67-8.67s):** Each wall segment lights up individually in sequence. Labels appear with leader lines: "input validation", "error format", "edge case: null", "return type". Each label fades in over 10 frames.
6. **Frame 260-280 (8.67-9.33s):** Counter appears: "Constraints defined: 4" / "Behaviors constrained: ∞"
7. **Frame 280-300 (9.33-10s):** Hold. All walls glowing. The simplicity of 4 constraints versus the perfect shape.

### Typography
- Wall labels: JetBrains Mono, 10px, `#D9944A` at 0.6
- Constraint counter: JetBrains Mono, 16px, `#D9944A` at 0.7
- Behaviors label: JetBrains Mono, 12px, `#64748B` at 0.4

### Easing
- Wall draw: `easeOut(cubic)` per segment, 15 frames each
- Liquid physics: custom velocity-based (gravity + damping)
- Particle merge: `easeInOut(quad)` over 30 frames
- Wall glow activation: `easeOut(quad)` over 10 frames per wall
- Label fade: `easeOut(quad)` over 10 frames
- Counter fade: `easeOut(quad)` over 15 frames

## Narration Sync
> "In injection molding, precision comes from the walls. The material just flows until it's constrained."
> "This maps directly to PDD."

Segment: `part4_004`

- **18:58** ("precision comes from the walls"): Liquid flowing chaotically, bouncing off walls
- **19:02** ("The material just flows"): Particles swirling freely inside cavity
- **19:04** ("until it's constrained"): Liquid settles into perfect shape, walls glow
- **19:06** ("This maps directly to PDD"): Wall labels appear — test names mapping to wall segments

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <RadialGradient center={[960, 480]} color="#0F172A" opacity={0.15} />

    {/* Mold cavity — walls draw in */}
    <Sequence from={0}>
      <MoldCavity shape={bracketShape}
        center={[960, 480]} size={[500, 550]}
        wallColor="#D9944A" wallOpacity={0.4} wallWidth={4}
        interiorColor="#0F172A" interiorOpacity={0.1}
        drawDuration={30} segmentFlash={true} />
    </Sequence>

    {/* Liquid simulation */}
    <Sequence from={30}>
      <LiquidSimulation
        cavityShape={bracketShape}
        entryPoint={[960, 205]} gateWidth={30}
        particleCount={70} particleSizeRange={[5, 12]}
        color="#94A3B8" opacity={0.3}
        gravity={0.3} damping={0.85}
        flowDuration={120} settleDuration={30}
        mergeToSolid={true} solidOpacity={0.2} />
    </Sequence>

    {/* Wall labels — sequential reveal */}
    <Sequence from={200}>
      <WallLabel wall="top" text="input validation"
        font="JetBrains Mono" size={10}
        color="#D9944A" opacity={0.6}
        leaderLine={true} delay={0} fadeDuration={10} />
      <WallLabel wall="right" text="error format"
        delay={15} fadeDuration={10} />
      <WallLabel wall="bottom" text="edge case: null"
        delay={30} fadeDuration={10} />
      <WallLabel wall="left" text="return type"
        delay={45} fadeDuration={10} />
    </Sequence>

    {/* Wall glow activation */}
    <Sequence from={150}>
      <WallGlow shape={bracketShape}
        color="#D9944A" opacity={0.15}
        blur={30} pulsePeriod={40} />
    </Sequence>

    {/* Constraint counter */}
    <Sequence from={260}>
      <FadeIn duration={15}>
        <Text text="Constraints defined: 4"
          font="JetBrains Mono" size={16}
          color="#D9944A" opacity={0.7}
          x={960} y={920} align="center" />
        <Text text="Behaviors constrained: ∞"
          font="JetBrains Mono" size={12}
          color="#64748B" opacity={0.4}
          x={960} y={950} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "mold_wall_constraint",
  "walls": [
    { "segment": "top", "testLabel": "input validation", "color": "#D9944A" },
    { "segment": "right", "testLabel": "error format", "color": "#D9944A" },
    { "segment": "bottom", "testLabel": "edge case: null", "color": "#D9944A" },
    { "segment": "left", "testLabel": "return type", "color": "#D9944A" }
  ],
  "liquidSimulation": {
    "particleCount": 70,
    "gravity": 0.3,
    "damping": 0.85
  },
  "constraintCount": 4,
  "metaphor": "Tests are walls — they constrain LLM output into correct shape without specifying every point",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_004"]
}
```

---
