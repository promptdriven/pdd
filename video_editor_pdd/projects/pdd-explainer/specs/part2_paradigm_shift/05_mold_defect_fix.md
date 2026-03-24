[Remotion]

# Section 2.5: Mold Defect Fix — Fix the Mold, Not the Part

**Tool:** Remotion
**Duration:** ~17s (510 frames @ 30fps)
**Timestamp:** 1:07 - 1:24

## Visual Description

An animated sequence showing the core insight of injection molding applied to defects. A stylized cross-section of an injection mold produces parts on a conveyor. A defect appears in one of the parts — a visible flaw, highlighted in red. Instead of someone patching the individual part, an engineer icon adjusts the mold wall itself. The mold glows briefly. New parts eject — all perfect. The defective part slides off the conveyor into a discard bin. A counter ticks: 1... 10... 100... 10,000... showing unlimited perfect production.

The animation uses clean geometric shapes in the project's navy-black palette — no photorealism. The mold is a stylized cross-section, parts are simple geometric shapes, and the defect is a visible distortion.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold Cross-Section
- Position: centered at (960, 400)
- Outer shell: rounded rectangle 400×200px, `#334155` at 0.6, 2px stroke
- Inner cavity: precise geometric shape (rounded rectangle with notch), `#0F172A`
- Mold walls: `#D9944A` at 0.5, 3px lines — the constraints
- Injection nozzle: small triangle at top, `#64748B` at 0.4

#### Conveyor Belt
- Position: y: 650, spanning x: 200 to x: 1720
- Belt surface: `#1E293B` at 0.4, with subtle moving hash marks
- Direction: left to right

#### Parts on Conveyor
- Shape: matches mold cavity — small rounded rectangles, 40×25px
- Normal color: `#4A90D9` at 0.5
- Defective part: same shape but with visible distortion, highlighted `#EF4444` at 0.6

#### Engineer Icon (adjusting mold)
- Position: to the right of the mold at (1200, 380)
- Simple human silhouette icon, `#E2E8F0` at 0.4
- Wrench/tool icon near the mold wall, `#FBBF24` at 0.6

#### Production Counter
- Position: upper-right at (1600, 150)
- "Parts produced:" — Inter, 12px, `#94A3B8` at 0.5
- Counter value: JetBrains Mono, 28px, bold, `#4ADE80`

### Animation Sequence
1. **Frame 0-60 (0-2s):** Mold cross-section visible. Liquid flows in (amber shimmer). A part ejects downward onto conveyor. Counter: 1.
2. **Frame 60-120 (2-4s):** More parts eject in rhythm. Counter ticks up: 2, 3, 4... Parts slide right on conveyor. All identical, all perfect.
3. **Frame 120-180 (4-6s):** A defective part ejects — visible distortion, red highlight. It sits on the conveyor. Counter pauses. A red pulse emanates from the defect.
4. **Frame 180-270 (6-9s):** Engineer icon slides in from right. Wrench icon moves toward the mold wall. The mold wall glows `#FBBF24` at the adjustment point. A subtle change to the wall shape.
5. **Frame 270-360 (9-12s):** Engineer icon slides away. The mold produces a new part — perfect. Then another. Counter resumes: 5, 6, 7... The defective part slides off the conveyor edge into a discard bin (fades out).
6. **Frame 360-510 (12-17s):** Production accelerates. Counter speeds up: 10... 100... 1,000... 10,000. Parts stream across the conveyor. All perfect. The mold walls pulse with quiet authority.

### Typography
- Counter label: Inter, 12px, `#94A3B8` at 0.5
- Counter value: JetBrains Mono, 28px, bold, `#4ADE80`

### Easing
- Part ejection: `easeOut(quad)` over 15 frames
- Conveyor movement: linear, constant speed
- Defect pulse: `easeInOut(sine)` over 20 frames
- Engineer slide-in: `easeOut(cubic)` over 20 frames
- Mold wall glow: `easeInOut(quad)` over 15 frames
- Counter acceleration: `easeIn(quad)` — starts slow, speeds up

## Narration Sync
> "And when there's a defect?"
> "You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again."
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."

Segments: `part2_paradigm_shift_008`, `part2_paradigm_shift_009`, `part2_paradigm_shift_010`

- **1:07** ("when there's a defect"): Defective part appears on conveyor
- **1:09** ("don't patch individual parts"): Engineer adjusts the mold wall
- **1:16** ("This is the real shift"): Counter accelerates, all parts perfect

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={510}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />

    {/* Mold cross-section */}
    <MoldCrossSection
      center={[960, 400]}
      outerSize={[400, 200]}
      wallColor="#D9944A" wallOpacity={0.5}
      shellColor="#334155" shellOpacity={0.6}
      cavityColor="#0F172A" />

    {/* Conveyor belt */}
    <ConveyorBelt
      y={650} xStart={200} xEnd={1720}
      color="#1E293B" opacity={0.4}
      speed={2} />

    {/* Part production sequence */}
    <PartProduction
      moldCenter={[960, 400]}
      conveyorY={650}
      partShape="rounded_rect" partSize={[40, 25]}
      normalColor="#4A90D9" normalOpacity={0.5}
      ejectionInterval={40}
      defectAtPart={5}
      defectColor="#EF4444" />

    {/* Engineer fixing mold */}
    <Sequence from={180} durationInFrames={90}>
      <EngineerIcon
        position={[1200, 380]}
        toolPosition={[1080, 400]}
        color="#E2E8F0" opacity={0.4}
        toolColor="#FBBF24" toolOpacity={0.6}
        slideFrom="right" slideDuration={20} />
    </Sequence>

    {/* Mold wall glow on fix */}
    <Sequence from={240}>
      <MoldWallGlow
        position={[860, 400]} width={20}
        color="#FBBF24" opacity={0.6}
        duration={15} />
    </Sequence>

    {/* Production counter */}
    <ProductionCounter
      position={[1600, 150]}
      labelFont="Inter" labelSize={12}
      valueFont="JetBrains Mono" valueSize={28}
      valueColor="#4ADE80"
      pauseAtDefect={{ frame: 120, duration: 150 }}
      accelerateFrom={360} />
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "mold_defect_fix",
  "elements": {
    "mold": { "type": "cross_section", "wallColor": "#D9944A" },
    "conveyor": { "type": "belt", "direction": "left_to_right" },
    "parts": { "normalColor": "#4A90D9", "defectColor": "#EF4444" },
    "engineer": { "color": "#E2E8F0", "toolColor": "#FBBF24" },
    "counter": { "maxValue": "10000+", "color": "#4ADE80" }
  },
  "narrativeArc": "defect_found → fix_mold → all_future_parts_perfect",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part2_paradigm_shift_008", "part2_paradigm_shift_009", "part2_paradigm_shift_010"]
}
```

---
