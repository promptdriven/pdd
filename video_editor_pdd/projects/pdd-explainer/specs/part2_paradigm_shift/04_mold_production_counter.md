[Remotion]

# Section 2.4: Mold Production Counter — Parts Ejecting

**Tool:** Remotion
**Duration:** ~11s (330 frames @ 30fps)
**Timestamp:** 1:08 - 1:19

## Visual Description

An animated sequence showing injection molded parts ejecting in rapid succession. A stylized side-view cross-section of a mold opens, and identical plastic parts (simplified geometric shapes — rounded rectangles) pop out one after another, falling into a growing pile below.

A large counter in the lower-right ticks up rapidly: 1 → 10 → 100 → 1,000 → 10,000. The counter accelerates exponentially. Each part is identical in shape but slightly randomized in rotation as it falls — emphasizing "unlimited identical parts." The mold itself stays perfectly still, glowing faintly to show it's the constant.

Background is dark industrial with a subtle grid. The mold is rendered in cool steel-blue, parts in warm amber. A faint defect marker (red outline) appears on one part near the end, setting up the next beat.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid: subtle 40px grid, `#1E293B` at 0.04

### Chart/Visual Elements

#### Mold Cross-Section
- Position: center-left, y: 300
- Steel casing: `#64748B`, 4px stroke, rounded rectangle 300x200
- Cavity shape: inner rounded rectangle cutout, `#334155` fill
- Glow: `#4A90D9` at 0.1, 8px blur around mold outline

#### Ejected Parts
- Shape: rounded rectangle 60x40, fill `#D9944A`, 2px stroke `#B8732A`
- Spawn from mold opening, fall with gravity + slight rotation
- Each part identical in shape, randomized rotation (±15°)
- Parts accumulate in pile below mold (y: 700+)

#### Counter
- Position: lower-right (x: 1600, y: 850)
- Font: JetBrains Mono, 64px, bold, `#E2E8F0`
- Counts: 1 → 10 → 100 → 1,000 → 10,000
- Label below: "identical parts" — Inter, 16px, `#94A3B8`

#### Defect Marker (end of sequence)
- One part at ~frame 300 gets a red outline: `#EF4444`, 3px, dashed
- Small "!" icon appears next to it: `#EF4444`, 14px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold cross-section fades in. Glow pulses once.
2. **Frame 30-60 (1-2s):** First part ejects. Counter: 1. Part falls slowly.
3. **Frame 60-120 (2-4s):** Parts eject faster. Counter accelerates: 10 → 100. Parts pile up.
4. **Frame 120-210 (4-7s):** Rapid-fire ejection. Counter: 1,000 → 10,000. Parts blur into continuous stream.
5. **Frame 210-270 (7-9s):** Ejection slows. Pile is substantial. Counter holds at 10,000.
6. **Frame 270-300 (9-10s):** One last part ejects with red defect outline. "!" appears.
7. **Frame 300-330 (10-11s):** Hold on defect part. Counter dims slightly. Mold still glows.

### Typography
- Counter: JetBrains Mono, 64px, bold (700), `#E2E8F0`
- Counter label: Inter, 16px, regular (400), `#94A3B8`
- Defect marker: Inter, 14px, bold, `#EF4444`

### Easing
- Part ejection: `easeOut(quad)` for each spawn
- Part fall: `easeIn(quad)` (gravity simulation)
- Counter increment: `easeOut(expo)` for number transitions
- Defect marker appear: `easeOut(back)` (slight overshoot)

## Narration Sync
> "Make the mold once. Produce unlimited identical parts. Refine the mold once. Every future part improves automatically."
> "And when there's a defect?"

Segments: `part2_paradigm_shift_007`, `part2_paradigm_shift_008`

- **1:08** (67.80s): Parts begin ejecting — "Make the mold once"
- **1:17** (76.94s): Counter at 10,000 — "Every future part improves automatically"
- **1:18** (78.42s): Defect part appears — "when there's a defect?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={330}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <SubtleGrid spacing={40} color="#1E293B" opacity={0.04} />

    {/* Mold cross-section */}
    <MoldCrossSection
      x={600} y={300} width={300} height={200}
      casingColor="#64748B" cavityColor="#334155"
      glowColor="#4A90D9" glowOpacity={0.1}
    />

    {/* Part ejection system */}
    <Sequence from={30}>
      <PartEjector
        spawnX={600} spawnY={500}
        partColor="#D9944A" partStroke="#B8732A"
        partSize={{ w: 60, h: 40 }}
        schedule={[
          { frame: 0, count: 1, rate: 'slow' },
          { frame: 30, count: 10, rate: 'medium' },
          { frame: 90, count: 100, rate: 'fast' },
          { frame: 120, count: 1000, rate: 'rapid' },
          { frame: 150, count: 10000, rate: 'blur' },
        ]}
      />
    </Sequence>

    {/* Counter */}
    <Sequence from={30}>
      <AnimatedCounter
        x={1600} y={850} font="JetBrains Mono" size={64}
        color="#E2E8F0" target={10000}
        label="identical parts" labelColor="#94A3B8"
      />
    </Sequence>

    {/* Defect part */}
    <Sequence from={270}>
      <DefectPart
        x={620} y={680}
        outlineColor="#EF4444" dashPattern={[6, 4]}
        iconSize={14}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_infographic",
  "elements": [
    { "id": "mold", "shape": "cross_section", "color": "#64748B", "role": "constant_specification" },
    { "id": "parts", "shape": "rounded_rect", "color": "#D9944A", "role": "generated_output" },
    { "id": "counter", "values": [1, 10, 100, 1000, 10000], "role": "scale_indicator" },
    { "id": "defect", "color": "#EF4444", "role": "flaw_transition" }
  ],
  "narrationSegments": ["part2_paradigm_shift_007", "part2_paradigm_shift_008"]
}
```

---
