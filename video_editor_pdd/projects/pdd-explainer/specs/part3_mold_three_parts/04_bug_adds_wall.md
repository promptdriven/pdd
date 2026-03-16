[Remotion]

# Section 3.3: Bug Adds a Wall — The Ratchet Effect

**Tool:** Remotion
**Duration:** ~20s (600 frames @ 30fps)
**Timestamp:** 13:42 – 14:02

## Visual Description
An animated sequence demonstrating PDD's core ratchet mechanic. A simplified mold with existing test walls is shown. A bug appears as a red spark inside the generated code area. Instead of patching the code, a new amber wall brick materializes — the bug becomes a permanent constraint. The code regenerates (liquid refills the mold), and the bug is gone. Then time advances: a counter shows "Generation 1 → 2 → 3 → 4 → 5" and each generation inherits all accumulated walls. The wall stack only grows. A ratchet gear icon clicks forward with each generation, never backward. The visual establishes that tests are monotonically increasing capital.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- Grid lines: None

### Chart/Visual Elements
- **Mold cavity:** Left-center (x: 160–760), 400px tall (y: 250–650)
  - 4 existing test wall bricks (pre-loaded), `#D9944A` at 0.25, labeled
  - Interior filled with code-colored particles (`#6B7C93` at 0.3)
- **Bug spark:** Red pulsing dot, 12px, `#EF4444` with glow `rgba(239,68,68,0.4)`, appears at ~(500, 450) inside the code area
- **Bug label:** "BUG" in small caps, `#EF4444`, 14px, positioned above spark
- **New wall brick:** 5th brick, materializes with emphasis — `#D9944A` with bright flash
  - Label: `assert no_duplicate_keys(config)`
- **Regeneration animation:** Code particles dissolve, cavity empties, refills with fresh particles — no red spark this time
- **Ratchet gear:** Right side at (1300, 400), 120px diameter
  - Gear outline: `#D9944A` at 0.4, 2px stroke
  - Teeth click forward with each generation increment
  - Arrow showing one-way rotation
- **Generation counter:** Below gear at (1300, 560)
  - "Generation N" — ticks from 1 to 5
  - Wall count indicator: "4 walls → 5 → 6 → 7 → 8"
- **Ratchet label:** "Tests only accumulate. The mold only gets more precise." — bottom center, y=850

### Animation Sequence
1. **Frame 0–30 (0–1.0s):** Mold cavity with 4 existing walls fades in. Interior filled with code particles. Everything looks stable.
2. **Frame 30–75 (1.0–2.5s):** Bug spark appears with a flash — red dot pulses, "BUG" label fades in above it. Particles near the bug turn slightly red. Synced with "Now watch what happens when you find a bug..."
3. **Frame 75–135 (2.5–4.5s):** Instead of touching the code, a new wall brick slides in from the left and locks into position as the 5th brick. Bright amber flash on arrival. The bug spark shrinks and extinguishes as the wall appears. Synced with "...you don't patch the code. You add a wall."
4. **Frame 135–195 (4.5–6.5s):** Regeneration: all code particles dissolve outward (scatter animation). Cavity is briefly empty (0.5s). Fresh particles flow back in from above — clean, no red. The 5th wall glows briefly to confirm it's constraining the new generation.
5. **Frame 195–270 (6.5–9.0s):** Ratchet gear appears on right with draw-on animation. "Generation 1" counter shows. Gear teeth are highlighted.
6. **Frame 270–450 (9.0–15.0s):** Time-lapse: generation counter ticks 2→3→4→5 (45 frames each). With each tick:
   - Gear clicks forward one tooth (30° rotation) with a mechanical click
   - A new wall brick adds to the stack (stack grows from 5→6→7→8)
   - Brief code particle regeneration flash
   - Wall count updates
   Synced with "That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."
7. **Frame 450–540 (15.0–18.0s):** Ratchet label types on at bottom: "Tests only accumulate. The mold only gets more precise." Gear maintains subtle idle rotation (very slow, 1° per second).
8. **Frame 540–600 (18.0–20.0s):** Hold. All elements stable. Wall stack has gentle amber ambient glow. Arrow on gear pulses to emphasize one-way nature.

### Typography
- Wall brick labels: JetBrains Mono, 12px, `#D9944A` at 0.8 opacity
- "BUG" label: Inter Bold, 14px, `#EF4444`, letter-spacing 2px
- Generation counter: Inter SemiBold, 24px, `#FFFFFF`
- Wall count: Inter Regular, 16px, `#D9944A`
- Ratchet label: Inter Medium, 18px, `#FFFFFF` at 0.7 opacity

### Easing
- Bug spark appearance: `easeOutExpo` (flash)
- New wall slide-in: `spring({ damping: 12, stiffness: 120 })`
- Particle dissolution: `easeOutCubic`
- Particle refill: `easeInOutCubic`
- Gear rotation: `easeOutBack(1.5)` (mechanical overshoot)
- Counter increment: `easeOutQuad`
- Label type-on: linear

## Narration Sync
> "Now watch what happens when you find a bug..."

> "...you don't patch the code. You add a wall."

> "That wall is permanent. That bug can never occur again — not in this generation, not in any future generation."

> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."

> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={600}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Initial mold with 4 walls */}
    <Sequence from={0} durationInFrames={30}>
      <MoldCavity walls={initialWalls} codeParticles={true} />
    </Sequence>

    {/* Bug appears */}
    <Sequence from={30} durationInFrames={45}>
      <BugSpark x={500} y={450} />
      <FadeIn><Label text="BUG" color="#EF4444" x={500} y={420} /></FadeIn>
    </Sequence>

    {/* New wall materializes, bug extinguishes */}
    <Sequence from={75} durationInFrames={60}>
      <NewWallBrick
        label="assert no_duplicate_keys(config)"
        color="#D9944A"
        flash={true}
      />
      <BugExtinguish />
    </Sequence>

    {/* Regeneration */}
    <Sequence from={135} durationInFrames={60}>
      <ParticleDissolve />
      <Sequence from={15}>
        <ParticleRefill clean={true} />
      </Sequence>
    </Sequence>

    {/* Ratchet gear + generation counter */}
    <Sequence from={195} durationInFrames={345}>
      <RatchetGear
        cx={1300}
        cy={400}
        radius={60}
        color="#D9944A"
      />
      <GenerationCounter
        from={1}
        to={5}
        x={1300}
        y={560}
        wallCounts={[5, 6, 7, 8]}
        framePer={45}
        startFrame={270}
      />
    </Sequence>

    {/* Ratchet label */}
    <Sequence from={450} durationInFrames={90}>
      <TypeOnText
        text="Tests only accumulate. The mold only gets more precise."
        y={850}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "initialWalls": [
    "assert output != None",
    "assert len(result) > 0",
    "assert response.status == 200",
    "assert total == sum(items)"
  ],
  "newWall": "assert no_duplicate_keys(config)",
  "generations": [
    { "gen": 1, "wallCount": 5 },
    { "gen": 2, "wallCount": 6 },
    { "gen": 3, "wallCount": 7 },
    { "gen": 4, "wallCount": 8 },
    { "gen": 5, "wallCount": 8 }
  ],
  "ratchetGear": {
    "center": { "x": 1300, "y": 400 },
    "radius": 60,
    "degreesPerClick": 30,
    "direction": "clockwise-only"
  }
}
```

---
