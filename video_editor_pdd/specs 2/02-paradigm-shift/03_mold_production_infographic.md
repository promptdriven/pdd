[Remotion] Mold-to-Parts Production Flow — Animated Infographic

# Section 2.2: Mold Production Infographic — "Design Once, Produce Unlimited"

**Tool:** Remotion
**Duration:** ~20s
**Timestamp:** 0:45 - 1:05

## Visual Description
An animated infographic overlay showing the injection molding metaphor as a process flow. On the left, a single glowing mold shape (stylized rectangle with cavity cutout) pulses with importance. From its right edge, a conveyor-belt animation streams identical small parts flowing rightward — each part is a simple rounded rectangle in white that pops into existence as it exits the mold. A counter in the corner rapidly increments from 1 to 1000+. At the 10s mark, a red "X" appears on one of the parts (defect), then a dotted line traces back to the mold, and a wrench icon appears on the mold — illustrating "fix the mold, not the parts." The defective part dissolves and all subsequent parts emerge corrected.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Infographic region: centered, 1400x500px area at (260, 290) to (1660, 790)
- Backing panel: rounded rect, rgba(15, 23, 42, 0.75), blur(8px), border-radius 16px

### Chart/Visual Elements
- Mold shape: 200x300px stylized rectangle at (320, 390)
  - Fill: #334155 with #F97316 border glow (4px)
  - Cavity cutout: 120x80px rounded rectangle, darker fill
  - Label: "MOLD" — centered below, #F97316
- Conveyor belt: horizontal line from x=520 to x=1580, y=540
  - Belt: 4px solid #475569, animated dash pattern moving rightward
  - Support legs: two vertical lines at x=520 and x=1580
- Parts: rounded rectangles, 60x40px each, #E2E8F0 fill, #CBD5E1 border
  - Spacing: 80px apart on conveyor
  - Pop-in animation: scale 0→1 as each exits mold
- Counter: top-right of infographic region, (1500, 320)
  - Format: "×1,000+" — monospace numerals
- Defect indicator: red "✗" mark on one part, #EF4444
- Trace-back line: dashed line from defective part back to mold, #EF4444
- Wrench icon: 32x32px, appears on mold, #22C55E

### Animation Sequence
1. **Frame 0-30 (0-1s):** Backing panel fades in. Mold shape fades in with border glow pulsing.
2. **Frame 20-40 (0.67-1.33s):** "MOLD" label fades in. Conveyor belt draws from left to right.
3. **Frame 40-180 (1.33-6s):** Parts begin streaming from mold — one every 15 frames (0.5s). Each pops in with spring animation. Counter increments with each part.
4. **Frame 180-240 (6-8s):** Counter accelerates — skip-counting to suggest massive scale. Parts stream faster (one every 5 frames).
5. **Frame 240-270 (8-9s):** Counter hits "×1,000+". Stream pauses.
6. **Frame 270-290 (9-9.67s):** Red "✗" appears on one part. Part flashes red.
7. **Frame 290-330 (9.67-11s):** Dashed trace-back line animates from defective part to mold.
8. **Frame 330-360 (11-12s):** Wrench icon appears on mold (spring scale-in). Mold border flashes green.
9. **Frame 360-390 (12-13s):** Defective part dissolves (opacity 1→0, scale 1→0.5). New corrected parts resume streaming.
10. **Frame 390-600 (13-20s):** Hold with corrected stream, then entire infographic fades out — opacity 1→0.

### Typography
- "MOLD" label: Inter Bold, 20px, #F97316, letter-spacing 0.15em
- Counter: JetBrains Mono Bold, 36px, #FFFFFF
- Counter prefix "×": Inter Medium, 24px, #94A3B8

### Easing
- Mold fade-in: `easeOutCubic`
- Part pop-in: `spring({ damping: 14, stiffness: 220 })`
- Counter increment: `easeOutQuad`
- Red flash: `easeInOutSine` (pulse)
- Trace-back line: `easeInOutCubic`
- Wrench icon: `spring({ damping: 10, stiffness: 180 })`

## Narration Sync
> "Design the mold once, produce unlimited identical parts. Find a defect? Fix the mold — not every individual part. The cost is in the specification, not the production."

Parts stream as "produce unlimited identical parts" is spoken. Defect sequence triggers on "Find a defect?" Wrench appears on "Fix the mold."

## Code Structure (Remotion)
```typescript
<Sequence from={MOLD_START} durationInFrames={600}>
  {/* Backing panel */}
  <AbsoluteFill>
    <BackingPanel
      bounds={{ x: 260, y: 290, w: 1400, h: 500 }}
      opacity={interpolate(frame, [0, 30, 570, 600], [0, 0.75, 0.75, 0])}
      blur={8}
      borderRadius={16}
    />

    {/* Mold shape */}
    <MoldShape
      position={[320, 390]}
      opacity={interpolate(frame, [0, 30], [0, 1])}
      glowColor="#F97316"
      glowPulse={interpolate(Math.sin(frame * 0.08), [-1, 1], [0.6, 1.0])}
    />

    {/* Conveyor belt */}
    <ConveyorBelt
      from={520} to={1580} y={540}
      drawProgress={interpolate(frame, [20, 40], [0, 1], { extrapolateRight: 'clamp' })}
      dashOffset={frame * 2}
    />

    {/* Streaming parts */}
    <PartStream
      startFrame={40}
      moldExitX={520}
      conveyorEndX={1580}
      y={510}
      partSize={[60, 40]}
      normalInterval={15}
      fastInterval={5}
      fastStartFrame={180}
      defectFrame={270}
      fixFrame={360}
    />

    {/* Counter */}
    <PartCounter
      position={[1500, 320]}
      startFrame={40}
      style={{ opacity: interpolate(frame, [40, 60, 570, 600], [0, 1, 1, 0]) }}
    />

    {/* Defect trace-back */}
    <Sequence from={290} durationInFrames={40}>
      <DashedTraceLine
        from={defectPartPosition}
        to={[320, 390]}
        color="#EF4444"
        drawProgress={interpolate(frame, [0, 40], [0, 1])}
      />
    </Sequence>

    {/* Wrench fix icon */}
    <Sequence from={330} durationInFrames={270}>
      <WrenchIcon
        position={[320, 360]}
        scale={spring({ frame: frame - 330, fps: 30, config: { damping: 10, stiffness: 180 } })}
        color="#22C55E"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "mold_position": [320, 390],
  "conveyor_y": 540,
  "conveyor_range": [520, 1580],
  "part_size": [60, 40],
  "part_color": "#E2E8F0",
  "normal_interval_frames": 15,
  "fast_interval_frames": 5,
  "max_count_display": "×1,000+",
  "defect_frame_offset": 270,
  "fix_frame_offset": 360,
  "total_frames": 600,
  "fps": 30
}
```

---
