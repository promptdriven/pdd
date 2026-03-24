[Remotion]

# Section 3.7: Ratchet Effect — Walls Only Accumulate

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 2:06 - 2:20

## Visual Description

A time-lapse animation of the mold accumulating walls over time. The mold starts with 3-4 walls, then rapidly gains more: each "bug found" event adds a new wall. A counter in the upper-right tracks the wall count: 4 → 7 → 12 → 18 → 25. The mold becomes increasingly precise — the cavity shape becomes more defined, more constrained.

Critically, no walls ever disappear. A subtle ratchet icon (a gear with a pawl) sits in the corner, clicking forward with each new wall. In the lower-right, `pdd test` output scrolls with green checkmarks accumulating — the test suite growing longer over time.

The visual rhythm is: pulse (bug), new wall appears, checkmark added, repeat. The pace accelerates — early walls appear slowly, later ones come in rapid succession, showing compound growth.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (center)
- Position: centered at (700, 500), 600×350px
- Initial walls: 4, spaced evenly, `#D9944A` at 0.4
- New walls animate in with amber flash, then settle to 0.6

#### Wall Counter
- Position: (1600, 100)
- Large number: Inter, 64px, bold, `#D9944A`
- Label below: "tests" — Inter, 14px, `#94A3B8` at 0.5

#### Ratchet Icon
- Position: (1600, 250), 60×60px
- Gear with pawl mechanism, `#D9944A` at 0.3
- Clicks forward (15° rotation) each time a wall is added
- Subtle mechanical click implied by the motion

#### Terminal Overlay
- Position: (1300, 500), 500×400px
- Scrolling `pdd test` output
- Green checkmarks: `#4ADE80`
- Test names in `#94A3B8` at 0.5

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold with 4 walls visible. Counter: 4.
2. **Frame 30-90 (1-3s):** Three new walls added (one every 20 frames). Counter: 4 → 7. Ratchet clicks 3×.
3. **Frame 90-180 (3-6s):** Five new walls (one every 18 frames). Counter: 7 → 12. Pace increasing.
4. **Frame 180-270 (6-9s):** Six new walls (one every 15 frames). Counter: 12 → 18. Faster.
5. **Frame 270-330 (9-11s):** Seven walls rapid-fire (one every 8 frames). Counter: 18 → 25. The mold is now highly precise.
6. **Frame 330-420 (11-14s):** Hold. All 25 walls visible and glowing. Terminal shows 25 passing tests. Counter pulses. Label: "Tests only accumulate. The mold only gets more precise."

### Typography
- Counter number: Inter, 64px, bold (700), `#D9944A`
- Counter label: Inter, 14px, `#94A3B8` at 0.5
- Terminal: JetBrains Mono, 10px, `#4ADE80` / `#94A3B8`
- Bottom label: Inter, 16px, `#D9944A` at 0.6, centered

### Easing
- New wall appear: `easeOut(back)` over 10 frames
- Counter increment: `easeOut(expo)` over 5 frames with slight scale pulse
- Ratchet click: `easeOut(quad)` 15° rotation over 5 frames
- Terminal scroll: linear, constant speed
- Final label: `easeOut(quad)` fade over 20 frames

## Narration Sync
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."
> "In traditional development, a bug fix helps one place. In PDD, a test prevents that bug everywhere, forever."

Segments: `part3_mold_three_parts_014`, `part3_mold_three_parts_015`

- **2:06** ("ratchet effect"): Time-lapse begins, walls accumulating
- **2:10** ("Tests only accumulate"): Acceleration visible, counter climbing
- **2:15** ("traditional development"): All walls visible, mold precise

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Mold with accumulating walls */}
    <MoldWithWalls cx={700} cy={500} width={600} height={350}>
      {WALL_TIMELINE.map((wall, i) => (
        <Sequence from={wall.frame} key={wall.id}>
          <NewWall
            position={wall.position}
            color="#D9944A"
            materializeDuration={10}
            easing="easeOut(back)" />
        </Sequence>
      ))}
    </MoldWithWalls>

    {/* Wall counter */}
    <AnimatedCounter
      x={1600} y={100}
      values={[4, 7, 12, 18, 25]}
      times={[0, 90, 180, 270, 330]}
      font="Inter" fontSize={64} color="#D9944A"
      label="tests" labelFont="Inter" labelSize={14} />

    {/* Ratchet icon */}
    <RatchetGear x={1600} y={250} size={60}
      color="#D9944A" opacity={0.3}
      clicks={WALL_TIMELINE.map(w => w.frame)}
      rotationPerClick={15} />

    {/* Terminal */}
    <Sequence from={30}>
      <TerminalScroll x={1300} y={500} width={500} height={400}
        command="pdd test"
        lines={TEST_NAMES.map(t => `✓ ${t}`)}
        stagger={16} color="#4ADE80" />
    </Sequence>

    {/* Bottom label */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <Text text="Tests only accumulate. The mold only gets more precise."
          font="Inter" size={16} color="#D9944A" opacity={0.6}
          x={960} y={940} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "ratchet_timelapse",
  "wallTimeline": [
    { "frame": 0, "count": 4, "phase": "initial" },
    { "frame": 90, "count": 7, "phase": "early_growth" },
    { "frame": 180, "count": 12, "phase": "mid_growth" },
    { "frame": 270, "count": 18, "phase": "acceleration" },
    { "frame": 330, "count": 25, "phase": "mature" }
  ],
  "wallColor": "#D9944A",
  "ratchetMetaphor": true,
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_three_parts_014", "part3_mold_three_parts_015"]
}
```

---
