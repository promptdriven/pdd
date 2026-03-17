[Remotion]

# Section 2.4: Defect → Fix the Mold — Not the Part

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 8:48 - 9:02

## Visual Description

An animated sequence demonstrating the key insight of mold-based manufacturing: when there's a defect, you fix the mold, not the individual part. The animation unfolds in three acts on a dark background.

**Act 1 — The Defect:** A simplified injection mold diagram (clean vector style, engineering-diagram aesthetic) sits center-screen. A plastic part ejects from the mold. A red highlight pulse appears on one edge of the part — a visible flaw. A magnifying glass icon zooms in on the defect, and a callout reads "Defect detected."

**Act 2 — Fix the Mold:** Instead of patching the part (which briefly flickers as a possibility, then fades with an X through it), the focus shifts to the mold itself. An engineer's cursor/tool adjusts a wall segment of the mold — the wall shifts by a few pixels with a subtle amber glow. The adjustment is small, precise. Label: "Fix the mold."

**Act 3 — Every Future Part:** New parts begin ejecting from the corrected mold. Each one is perfect — green checkmarks appear over them. The defective original part dissolves and is discarded. A counter ticks: "All future parts: fixed." The visual makes the argument: one fix, infinite benefit.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Faint drafting grid, 40px spacing, `#1E293B` at 0.04

### Chart/Visual Elements

#### Mold Diagram
- Center: (960, 400)
- Width: 400px, Height: 500px
- Outline stroke: `#475569` at 0.6, 2px
- Wall fill: `#D9944A` at 0.1
- Cavity: `#1E293B` at 0.3

#### Ejected Parts
- Shape: simplified rectangular part with notched edge, 80x50px
- Normal color: `#94A3B8` at 0.5
- Defective part: same shape with red highlight on one edge, `#EF4444` at 0.6
- Fixed parts: same shape with green checkmark overlay, `#5AAA6E` at 0.5

#### Defect Callout
- Red pulse ring around defect area, 16px radius, `#EF4444` at 0.4
- Magnifying glass icon: `#E2E8F0` at 0.5, 40x40px
- Label: "Defect detected" — Inter, 13px, `#EF4444` at 0.7

#### "Patch the part" (rejected approach)
- Ghost of a hand tool approaching the part, `#94A3B8` at 0.2
- Red X overlay: `#EF4444`, 2px stroke, 40x40px

#### Mold Adjustment
- Wall segment highlight: `#D9944A` at 0.3 → 0.6 during adjustment
- Cursor/wrench icon: `#E2E8F0` at 0.6, positioned at wall edge
- Wall slides 4px inward with amber glow trail
- Label: "Fix the mold" — Inter, 14px, semi-bold, `#D9944A` at 0.8

#### Fixed Parts Counter
- Position: lower-right, (1600, 900)
- "All future parts: fixed" — Inter, 14px, `#5AAA6E` at 0.6
- Small green checkmark icons accumulate

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold diagram draws itself. Clean, technical, centered.
2. **Frame 30-60 (1-2s):** A part ejects downward from the mold cavity. It slides to position below.
3. **Frame 60-100 (2-3.33s):** Red pulse appears on one edge of the ejected part. Magnifying glass icon appears, zooming in. "Defect detected" label fades in.
4. **Frame 100-140 (3.33-4.67s):** Brief flash — a ghost hand tool approaches the part (the "patch" approach). Red X strikes through it. The ghost fades. This is NOT how you fix it.
5. **Frame 140-200 (4.67-6.67s):** Focus shifts UP to the mold. A cursor/wrench icon appears at a wall segment. The wall highlights amber. The wall adjusts — shifts 4px — with a smooth amber glow trail. "Fix the mold" label appears.
6. **Frame 200-280 (6.67-9.33s):** New parts begin ejecting from the corrected mold. First part: green checkmark. Second part: green checkmark. Third: checkmark. They stack below.
7. **Frame 280-340 (9.33-11.33s):** The original defective part dissolves (opacity → 0, red particles scatter). "All future parts: fixed" label appears with counter.
8. **Frame 340-420 (11.33-14s):** Hold. Perfect parts continue appearing. The mold pulses with a satisfied amber glow. The argument is made.

### Typography
- "Defect detected": Inter, 13px, `#EF4444` at 0.7
- "Fix the mold": Inter, 14px, semi-bold (600), `#D9944A` at 0.8
- "All future parts: fixed": Inter, 14px, `#5AAA6E` at 0.6

### Easing
- Part ejection: `easeOut(cubic)` over 20 frames
- Red pulse: `easeInOut(sine)` on 20-frame cycle
- Ghost tool fade: `easeOut(quad)` over 15 frames
- Red X strike: `easeOut(back(1.3))` over 10 frames
- Wall adjustment: `easeInOut(cubic)` over 30 frames
- Green checkmark pop: `easeOut(back(1.5))` scale from 0 to 1, 10 frames
- Defective part dissolve: `easeIn(quad)` over 30 frames

## Narration Sync
> "And when there's a defect?"
> "You don't patch individual parts. You fix the mold. And that fix applies to every part you'll ever make again."

Segment: `part2_004`

- **8:48** ("And when there's a defect?"): Defect pulse appears on ejected part
- **8:51** ("You don't patch individual parts"): Ghost tool approaches, red X rejection
- **8:54** ("You fix the mold"): Cursor adjusts mold wall, amber glow
- **8:58** ("every part you'll ever make again"): Fixed parts eject with green checkmarks

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <DraftGrid spacing={40} color="#1E293B" opacity={0.04} />

    {/* Mold diagram */}
    <Sequence from={0}>
      <MoldDiagram
        center={[960, 400]} width={400} height={500}
        strokeColor="#475569" strokeWidth={2}
        wallFill="#D9944A" wallFillOpacity={0.1}
        cavityColor="#1E293B" cavityOpacity={0.3}
        drawDuration={30}
      />
    </Sequence>

    {/* Part ejection */}
    <Sequence from={30}>
      <EjectPart
        from={[960, 650]} to={[960, 780]}
        partWidth={80} partHeight={50}
        color="#94A3B8" opacity={0.5}
        duration={20}
      />
    </Sequence>

    {/* Defect highlight */}
    <Sequence from={60}>
      <DefectPulse position={[1000, 780]} radius={16}
        color="#EF4444" opacity={0.4}
        magnifyIcon magnifySize={40} />
      <Label text="Defect detected" color="#EF4444"
        opacity={0.7} position={[1060, 810]} size={13} />
    </Sequence>

    {/* Rejected: patch the part */}
    <Sequence from={100} durationInFrames={40}>
      <GhostTool position={[960, 780]} color="#94A3B8"
        opacity={0.2} fadeDuration={15} />
      <RedX position={[960, 780]} size={40}
        color="#EF4444" strokeWidth={2} />
    </Sequence>

    {/* Fix the mold */}
    <Sequence from={140}>
      <WallAdjustment
        moldCenter={[960, 400]}
        wallSegment="right_upper"
        adjustPx={4} direction="inward"
        cursorIcon="wrench" cursorColor="#E2E8F0"
        highlightColor="#D9944A"
        glowTrail duration={30}
      />
      <Label text="Fix the mold" color="#D9944A"
        opacity={0.8} position={[1200, 350]}
        size={14} weight={600} />
    </Sequence>

    {/* Fixed parts eject */}
    <Sequence from={200}>
      <FixedPartsSequence
        moldCenter={[960, 400]}
        partCount={5} interval={25}
        partColor="#94A3B8" checkColor="#5AAA6E"
        stackPosition={[960, 780]}
      />
    </Sequence>

    {/* Defective part dissolve */}
    <Sequence from={280}>
      <ParticleDissolve position={[860, 780]}
        color="#EF4444" duration={30} />
    </Sequence>

    {/* Counter label */}
    <Sequence from={300}>
      <FadeIn duration={20}>
        <Label text="All future parts: fixed" color="#5AAA6E"
          opacity={0.6} position={[1600, 900]} size={14} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "defect_fix_mold",
  "acts": [
    { "name": "defect", "frames": [60, 100], "element": "red_pulse_on_part" },
    { "name": "rejected_patch", "frames": [100, 140], "element": "ghost_tool_red_x" },
    { "name": "fix_mold", "frames": [140, 200], "element": "wall_adjustment_amber" },
    { "name": "fixed_parts", "frames": [200, 340], "element": "green_checkmark_parts" }
  ],
  "colors": {
    "defect": "#EF4444",
    "mold_wall": "#D9944A",
    "fixed": "#5AAA6E",
    "part": "#94A3B8"
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part2_004"]
}
```

---
