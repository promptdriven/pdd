[Remotion]

# Section 7.5: Dissolve Regenerate Loop — Code as Disposable Output

**Tool:** Remotion
**Duration:** ~6s (180 frames @ 30fps)
**Timestamp:** 0:13 - 0:19

## Visual Description

Continuing from the PDD triangle, the code block in the center of the triangle dissolves and regenerates. This happens three times in a subtle loop. Each regeneration produces slightly different code — different variable names, different line structure — but the triangle vertices (PROMPT, TESTS, GROUNDING) remain absolutely stable.

A subtle terminal ticker runs at the bottom: `pdd generate` → code appears → `pdd test` → `✓` → repeat. The repetition drives the point home: code is ephemeral output, the mold is permanent.

Each regeneration cycle, the code briefly flickers with a different tint (blue, then green, then amber) — echoing which vertex is "driving" that generation. But the result always passes.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: none

### Chart/Visual Elements

#### Triangle (persistent from 04_pdd_triangle)
- Same positions and styling as Section 7.4
- All vertices at steady glow — no animation, stable anchors
- Edge lines: 2px, `#334155` at 0.3

#### Center Code Block
- Position: centered at (960, 520), width 400px, height 200px
- Code: JetBrains Mono, 11px, `#E2E8F0` at 0.7
- 8-10 lines per generation
- Containment area: faint border `#334155` at 0.06

#### Dissolve/Regenerate Effect
- Dissolve: code characters scatter outward with decreasing opacity (particle effect)
- Regenerate: new code characters stream inward from triangle edges, assembling into lines
- Cycle 1 tint: `#60A5FA` at 0.05 (blue — prompt-driven)
- Cycle 2 tint: `#4ADE80` at 0.05 (green — test-driven)
- Cycle 3 tint: `#D9944A` at 0.05 (amber — grounding-driven)

#### Terminal Ticker
- Position: bottom center, (560, 980) to (1360, 1020)
- Background: transparent
- Font: JetBrains Mono, 11px, `#64748B` at 0.5
- Cycles: `pdd generate → ✓ → pdd generate → ✓ → pdd generate → ✓`

### Animation Sequence
1. **Frame 0-10 (0-0.3s):** Triangle stable from previous spec. Code block visible in center.
2. **Frame 10-50 (0.3-1.7s):** Cycle 1 — code dissolves (particles scatter, 15 frames). New code regenerates (streams in, 15 frames). Blue tint flash. Terminal: `pdd generate → ✓`. `easeInOut(cubic)`.
3. **Frame 50-60 (1.7-2s):** Brief hold. Code stable.
4. **Frame 60-100 (2-3.3s):** Cycle 2 — dissolve and regenerate. Different code. Green tint flash. Terminal: `pdd generate → ✓`.
5. **Frame 100-110 (3.3-3.7s):** Brief hold.
6. **Frame 110-150 (3.7-5s):** Cycle 3 — dissolve and regenerate. Different code again. Amber tint flash. Terminal: `pdd generate → ✓`.
7. **Frame 150-180 (5-6s):** Final hold. Code stable. Triangle glowing. Terminal shows final `✓`.

### Typography
- Code: JetBrains Mono, 11px, regular (400), `#E2E8F0`
- Terminal ticker: JetBrains Mono, 11px, regular (400), `#64748B`
- Checkmarks: `#4ADE80`

### Easing
- Dissolve scatter: `easeIn(quad)` over 15 frames
- Regenerate stream: `easeOut(cubic)` over 15 frames
- Tint flash: `easeInOut(sine)` — ramp up 5 frames, hold 5, ramp down 5
- Terminal text: `linear`, 10 frame delay between elements

## Narration Sync
> "Code is generated, verified, and disposable."
> "The code is just plastic."

Segments: `closing_003`, `closing_004`

- **0:13** ("Code is generated"): Cycle 1 dissolve/regenerate
- **0:14** ("verified"): Cycle 2 dissolve/regenerate, checkmark
- **0:15** ("and disposable"): Cycle 3 dissolve/regenerate
- **0:16** ("The code"): Final hold, code stable but unremarkable
- **0:19** ("is just plastic"): Triangle glows, code fades slightly in emphasis

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={180}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Persistent triangle from previous spec */}
    <TriangleFrame
      vertices={[[960, 200], [480, 750], [1440, 750]]}
      labels={["PROMPT", "TESTS", "GROUNDING"]}
      colors={["#60A5FA", "#4ADE80", "#D9944A"]}
      edgeColor="#334155" edgeOpacity={0.3}
      glowRadius={40} glowOpacity={0.15} />

    {/* Dissolve-regenerate loop */}
    {[0, 1, 2].map((cycle) => (
      <Sequence from={10 + cycle * 50} key={cycle}>
        <DissolveRegenerate
          oldCode={CODE_VARIANTS[cycle]}
          newCode={CODE_VARIANTS[cycle + 1]}
          dissolveDuration={15}
          regenDuration={15}
          tintColor={CYCLE_TINTS[cycle]}
          tintOpacity={0.05}
          center={[960, 520]}
          width={400} height={200}
          font="JetBrains Mono" fontSize={11} />
      </Sequence>
    ))}

    {/* Terminal ticker */}
    <TerminalTicker
      x={560} y={980} width={800}
      font="JetBrains Mono" fontSize={11}
      color="#64748B" opacity={0.5}
      checkColor="#4ADE80"
      cycles={3} cycleDelay={50} />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "chartId": "dissolve_regenerate_loop",
  "cycles": 3,
  "cycleTints": ["#60A5FA", "#4ADE80", "#D9944A"],
  "triangle": {
    "persistent": true,
    "source": "pdd_triangle"
  },
  "terminal": {
    "command": "pdd generate",
    "successIndicator": "✓"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["closing_003", "closing_004"]
}
```

---
