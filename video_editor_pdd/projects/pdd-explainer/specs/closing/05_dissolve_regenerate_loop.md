[Remotion]

# Section 7.5: Dissolve-Regenerate Loop — Code Is Ephemeral

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 24:43 - 24:51

## Visual Description

The PDD triangle from the previous beat persists — nodes glowing at their vertices, edges stable. But the code at the center begins cycling through dissolve-regenerate loops. The code lines scatter outward as particles, then new code streams back in, different but constrained to the same triangular shape. This repeats three times, each cycle faster than the last.

The triangle never moves. The nodes never flicker. The edges hold firm. Only the code changes — dissolving, regenerating, dissolving, regenerating. The visual thesis is unmistakable: **code is ephemeral, structure is permanent**.

In the bottom-right corner, a subtle terminal heartbeat loops: `pdd generate → ✓ → pdd generate → ✓`, matching the dissolve-regenerate rhythm.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A1225` (deep navy-black, continuous from previous beat)
- Radial glow: centered at (960, 520), `#1E293B` at 0.04, radius 600px (carried over)

### Chart/Visual Elements

#### Triangle (Persistent from 04_pdd_triangle)
- Same equilateral triangle, centered at (960, 520), side length 500px
- Vertices: (960, 280), (710, 713), (1210, 713)
- Edge stroke: 2px, `#475569` at 0.6, glow 4px at 0.06
- Nodes: same circles and labels as previous beat, pulsing gently
- **The triangle is completely static** — it does not animate during this sequence

#### Code Lines (Cycling)
- 8-10 thin horizontal lines clustered at center (960, 520)
- Widths vary: 60-180px, staggered vertically
- **Cycle 1 (slow):** Color `#94A3B8` at 0.15, unique width/offset pattern
- **Cycle 2 (medium):** Color `#94A3B8` at 0.15, different width/offset pattern
- **Cycle 3 (fast):** Color `#94A3B8` at 0.15, yet another pattern
- Each cycle produces visibly different code — different line counts, widths, positions

#### Particle Scatter Effect
- On dissolve: each code line breaks into 5-8 particles
- Particles drift outward radially from center, decelerating
- Color: `#94A3B8` at 0.1, fading to 0.0 over 15 frames
- Particles must NOT cross triangle edges — they dissipate before reaching the boundary

#### Terminal Heartbeat (Corner)
- Position: x: 1640, y: 980
- Text: cycles between `pdd generate → ✓`
- Font: JetBrains Mono, 10px, `#4A90D9` at 0.2
- Synced to dissolve-regenerate rhythm

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Triangle holds from previous beat. Code lines present at center.
2. **Frame 10-40 (0.33-1.33s):** **Cycle 1 — Dissolve:** Code lines break into particles, scatter outward. Terminal: `pdd generate`.
3. **Frame 40-70 (1.33-2.33s):** **Cycle 1 — Regenerate:** New code lines stream into center from edges inward. Different pattern. Terminal: `✓`.
4. **Frame 70-95 (2.33-3.17s):** **Cycle 2 — Dissolve:** Code scatters again, faster this time. Particles are smaller.
5. **Frame 95-120 (3.17-4s):** **Cycle 2 — Regenerate:** Different code lines appear. Terminal: `✓`.
6. **Frame 120-140 (4-4.67s):** **Cycle 3 — Dissolve:** Fastest cycle. Code scatters quickly.
7. **Frame 140-160 (4.67-5.33s):** **Cycle 3 — Regenerate:** Final code pattern appears. Terminal: `✓`.
8. **Frame 160-240 (5.33-8s):** Hold on final regeneration. Triangle stable. Code present but unremarkable. The loop has made its point.

### Typography
- Terminal heartbeat: JetBrains Mono, 10px, `#4A90D9` at 0.2
- All triangle labels persist from previous beat (no new typography)

### Easing
- Particle scatter: `easeOut(cubic)` radial velocity, 15 frames to dissipate
- Code stream-in: `easeOut(quad)` per line, stagger decreasing per cycle (6→4→2 frames)
- Cycle acceleration: Cycle 1 = 60 frames, Cycle 2 = 50 frames, Cycle 3 = 40 frames
- Terminal text swap: instant (no easing — crisp terminal feel)

## Narration Sync
> "Code is generated, verified, and disposable."

Segment: `closing_004`

- **24:43** ("Code is generated"): Cycle 1 begins — code dissolves and regenerates
- **24:45** ("verified"): Cycle 2 — terminal shows `✓`, tests pass
- **24:47** ("and disposable"): Cycle 3 — fastest dissolve, emphasizing disposability
- **24:49** (hold): Triangle stable, code unremarkable

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A1225' }}>
    <RadialGlow center={[960, 520]} radius={600}
      color="#1E293B" opacity={0.04} />

    {/* Persistent triangle — static */}
    <TriangleFrame vertices={[[960,280],[710,713],[1210,713]]}
      edgeColor="#475569" edgeOpacity={0.6} edgeWidth={2}
      glow={{ blur: 4, opacity: 0.06 }} />
    <NodeCircle center={[960, 280]} radius={20} fill="#4A90D9"
      pulse={{ min: 20, max: 22, period: 60 }} />
    <NodeCircle center={[710, 713]} radius={20} fill="#D9944A"
      pulse={{ min: 20, max: 22, period: 60 }} />
    <NodeCircle center={[1210, 713]} radius={20} fill="#5AAA6E"
      pulse={{ min: 20, max: 22, period: 60 }} />
    {/* Labels persist from previous sequence */}
    <TriangleLabels />

    {/* Cycle 1 — slow */}
    <Sequence from={0} durationInFrames={70}>
      <Sequence from={10} durationInFrames={30}>
        <ParticleScatter lines={codePattern1} center={[960, 520]}
          particlesPerLine={6} driftRadius={120}
          fadeDuration={15} easing="easeOut(cubic)" />
      </Sequence>
      <Sequence from={40} durationInFrames={30}>
        <CodeLines center={[960, 520]} lines={codePattern2}
          color="#94A3B8" opacity={0.15}
          stagger={6} fadeDuration={8} />
      </Sequence>
    </Sequence>

    {/* Cycle 2 — medium */}
    <Sequence from={70} durationInFrames={50}>
      <Sequence from={0} durationInFrames={25}>
        <ParticleScatter lines={codePattern2} center={[960, 520]}
          particlesPerLine={5} driftRadius={100}
          fadeDuration={12} easing="easeOut(cubic)" />
      </Sequence>
      <Sequence from={25} durationInFrames={25}>
        <CodeLines center={[960, 520]} lines={codePattern3}
          color="#94A3B8" opacity={0.15}
          stagger={4} fadeDuration={6} />
      </Sequence>
    </Sequence>

    {/* Cycle 3 — fast */}
    <Sequence from={120} durationInFrames={40}>
      <Sequence from={0} durationInFrames={20}>
        <ParticleScatter lines={codePattern3} center={[960, 520]}
          particlesPerLine={4} driftRadius={80}
          fadeDuration={10} easing="easeOut(cubic)" />
      </Sequence>
      <Sequence from={20} durationInFrames={20}>
        <CodeLines center={[960, 520]} lines={codePattern4}
          color="#94A3B8" opacity={0.15}
          stagger={2} fadeDuration={5} />
      </Sequence>
    </Sequence>

    {/* Terminal heartbeat — corner */}
    <TerminalHeartbeat x={1640} y={980}
      command="pdd generate" successMark="✓"
      font="JetBrains Mono" size={10}
      color="#4A90D9" opacity={0.2}
      cycleTimes={[40, 95, 140]} />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_loop",
  "diagramId": "dissolve_regenerate_loop",
  "baseTriangle": "pdd_triangle",
  "cycles": [
    { "id": 1, "duration_frames": 60, "speed": "slow" },
    { "id": 2, "duration_frames": 50, "speed": "medium" },
    { "id": 3, "duration_frames": 40, "speed": "fast" }
  ],
  "particleEffect": {
    "type": "radial_scatter",
    "particlesPerLine": [6, 5, 4],
    "driftRadius": [120, 100, 80]
  },
  "terminalHeartbeat": {
    "command": "pdd generate",
    "successMark": "✓"
  },
  "backgroundColor": "#0A1225",
  "narrationSegments": ["closing_004"]
}
```

---
