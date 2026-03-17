[Remotion]

# Section 3.3: Test Walls Constraint — Liquid Meets Boundaries

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 13:14 - 13:26

## Visual Description

A focused animation showing the injection molding process in action. Liquid material (representing code generation) enters the mold from the injection nozzle at the top and flows downward. The liquid is rendered as animated particles with fluid dynamics — turbulent, chaotic, swirling — using Perlin noise displacement. It flows freely through the cavity until it encounters the mold walls.

Each collision is dramatic: the liquid hits a wall segment, the wall flashes amber, and the liquid stops and redirects. The camera focuses on one specific collision — the "null → None" wall — where the liquid surges toward it, impacts, and the wall holds firm. A brief ripple animation shows the force of the collision absorbed by the wall.

As the liquid fills the cavity, the shape emerges — constrained entirely by the walls. The viewer understands viscerally: the walls define the output. The liquid (LLM generation) has no inherent shape; the tests give it form.

A small terminal overlay in the bottom-right shows `pdd generate user_parser` running, with green output lines appearing as the liquid fills.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none (focus on the mold)

### Chart/Visual Elements

#### Mold Structure (carried forward, centered at 960, 500)
- Walls: `#D9944A` at 0.4, 4px stroke
- Cavity: `#1E293B` at 0.15
- Wall labels visible but dimmed: JetBrains Mono, 9px, `#D9944A` at 0.3

#### Liquid Flow
- Particle system: 200+ particles, `#4A90D9` at 0.5
- Turbulence: Perlin noise displacement, scale 0.04, speed 0.03
- Trailing glow: 6px blur, `#4A90D9` at 0.2
- Flow direction: top-down from nozzle, then lateral as cavity fills

#### Wall Collision Effects
- Flash: wall segment brightens to `#D9944A` at 1.0, 2px expansion, over 6 frames
- Ripple: concentric arcs from impact point, `#D9944A` at 0.2, fading over 15 frames
- Particle redirect: particles bounce away from wall surface, losing velocity

#### Focus Collision — "null → None" Wall
- Camera zoom: 120% on the left wall region around y: 350
- Liquid surge toward wall: accelerated particle velocity
- Wall holds: flash + ripple + subtle screen shake (2px, 4 frames)
- Label "null → None" glows brighter: `#D9944A` at 1.0

#### Terminal Overlay
- Position: bottom-right, 320×140px
- Background: `#0F172A` at 0.85, 1px `#334155` border, rounded 6px
- Font: JetBrains Mono, 10px, `#94A3B8`
- Content: `$ pdd generate user_parser` followed by green output lines
- Green output: `#5AAA6E` at 0.7

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold visible from previous spec. Liquid begins entering from nozzle — first particles appear, swirling.
2. **Frame 30-90 (1-3s):** Liquid flows downward, turbulent. First collision with right wall — amber flash. Particles redirect left. Second collision with left wall — flash.
3. **Frame 90-150 (3-5s):** Camera zooms to focus on "null → None" wall. Liquid surges toward it. Impact — flash, ripple, screen shake. The wall holds firm. Label brightens.
4. **Frame 150-240 (5-8s):** Camera pulls back. Cavity continues filling. Multiple wall collisions in sequence — each wall constrains the flow. Terminal overlay appears, `pdd generate` running.
5. **Frame 240-300 (8-10s):** Cavity mostly filled. The liquid has taken the shape defined by the walls. Terminal shows green checkmarks.
6. **Frame 300-360 (10-12s):** Final shape solidifies. Walls glow softly. The constrained output is clean, precise. Hold.

### Typography
- Wall labels: JetBrains Mono, 9px, `#D9944A` at 0.3 → 1.0 on focus
- Terminal text: JetBrains Mono, 10px, `#94A3B8`
- Terminal output: JetBrains Mono, 10px, `#5AAA6E` at 0.7

### Easing
- Liquid particle flow: Perlin noise, `linear` base velocity
- Wall collision flash: `easeOut(expo)` over 6 frames
- Ripple expand: `easeOut(cubic)` over 15 frames, opacity fade
- Camera zoom: `easeInOut(cubic)` over 30 frames
- Screen shake: `easeOut(quad)` decay over 4 frames
- Terminal appear: `easeOut(cubic)` from y+20, 15 frames

## Narration Sync
> "Each test is a constraint. A boundary the generated code cannot cross."
> "And these walls matter more than you'd think."

Segment: `part3_003`

- **13:14** ("Each test is a constraint"): Liquid enters, first wall collision
- **13:18** ("A boundary the generated code cannot cross"): Focus on "null → None" wall, dramatic impact
- **13:22** ("And these walls matter more than you'd think"): Pull back to full cavity filling

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Mold structure carried forward */}
    <MoldCrossSection center={[960, 500]}
      width={600} height={700}
      wallColor="#D9944A" wallOpacity={0.4} wallWidth={4}
      cavityColor="#1E293B" cavityOpacity={0.15}
      labels={wallLabels} labelOpacity={0.3} />

    {/* Liquid particle system */}
    <LiquidFlow
      entryPoint={[960, 200]}
      particleCount={200}
      color="#4A90D9" opacity={0.5}
      noiseScale={0.04} noiseSpeed={0.03}
      trailGlow={{ blur: 6, opacity: 0.2 }}
      cavityBounds={moldCavityBounds}
    />

    {/* Wall collisions with flash effects */}
    <WallCollisionEffects
      wallSegments={wallSegments}
      flashColor="#D9944A" flashOpacity={1.0}
      rippleColor="#D9944A" rippleOpacity={0.2}
      rippleDuration={15}
    />

    {/* Focus zoom on null wall */}
    <Sequence from={90}>
      <CameraZoom target={[760, 350]} scale={1.2} duration={30}>
        <ScreenShake magnitude={2} duration={4} triggerAt={120} />
      </CameraZoom>
    </Sequence>

    {/* Pull back */}
    <Sequence from={150}>
      <CameraZoom target={[960, 500]} scale={1.0} duration={30} />
    </Sequence>

    {/* Terminal overlay */}
    <Sequence from={150}>
      <TerminalOverlay
        position={[1520, 880]} size={[320, 140]}
        commands={[
          { text: '$ pdd generate user_parser', color: '#94A3B8' },
          { text: '  Generating...', color: '#94A3B8', delay: 30 },
          { text: '  ✓ All 12 tests passing', color: '#5AAA6E', delay: 90 }
        ]}
        font="JetBrains Mono" fontSize={10}
        bgColor="#0F172A" bgOpacity={0.85}
        borderColor="#334155"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "fluid_simulation",
  "diagramId": "test_walls_constraint",
  "particleCount": 200,
  "liquidColor": "#4A90D9",
  "wallColor": "#D9944A",
  "focusWall": "null → None",
  "collisionEffects": ["flash", "ripple", "screen_shake"],
  "terminalCommands": [
    "pdd generate user_parser",
    "Generating...",
    "✓ All 12 tests passing"
  ],
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_003"]
}
```

---
