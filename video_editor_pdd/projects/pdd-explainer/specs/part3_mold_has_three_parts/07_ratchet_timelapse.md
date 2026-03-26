[Remotion]

# Section 3.7: Ratchet Effect — Walls Only Accumulate

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 1:20 - 1:34

## Visual Description

A time-lapse of the mold becoming more precise over time. The mold cross-section is centered, and new walls appear one by one in rapid succession — each bug found adds a wall. The walls only accumulate; none disappear. A counter in the corner tracks the wall count: 6 → 8 → 11 → 15 → 20.

In the lower-right, a subtle terminal shows `pdd test` output scrolling — green checkmarks accumulating. Each time a new wall appears, the mold cavity becomes more precisely shaped. The liquid (code generation) within the mold automatically conforms to the new constraints.

The visual feel is mechanical inevitability — a ratchet clicking, each click permanent.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 40px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (evolving)
- Same cross-section, but walls multiply over time
- Starting state: 6 walls (from earlier)
- Each new wall: `#D9944A` at 0.6, briefly flashes to 0.8 on appearance
- New wall positions: increasingly precise, filling gaps in the cavity

#### Wall Counter
- Position: top-right, x: 1700, y: 80
- "WALLS:" label — Inter, 12px, `#94A3B8` at 0.4
- Count number — JetBrains Mono, 36px, bold, `#D9944A` at 0.8
- Counter animates: 6 → 8 → 11 → 15 → 20

#### Terminal (scrolling tests)
- Position: bottom-right, 400×180px
- `pdd test` output scrolling upward
- Green checkmarks: `✓` in `#4ADE80`, test names in `#94A3B8`
- Scrolling speed increases as walls accumulate

#### Liquid (auto-conforming)
- Liquid inside cavity adjusts shape each time a new wall appears
- Brief ripple on each wall addition

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold with 6 walls visible. Counter shows "6". Terminal begins.
2. **Frame 30-90 (1-3s):** Two new walls appear (30 frames apart). Counter: 6 → 7 → 8. Liquid adjusts.
3. **Frame 90-180 (3-6s):** Three more walls appear (accelerating). Counter: 8 → 9 → 10 → 11. Test output scrolling.
4. **Frame 180-300 (6-10s):** Four more walls in quick succession. Counter: 11 → 13 → 15. Mold visibly more precise.
5. **Frame 300-360 (10-12s):** Five final walls burst in. Counter: 15 → 18 → 20. The mold is intricate and precise.
6. **Frame 360-420 (12-14s):** Hold. All 20 walls glow. Label: "Tests only accumulate. The mold only gets more precise."

### Typography
- Counter label: Inter, 12px, `#94A3B8` at 0.4
- Counter number: JetBrains Mono, 36px, bold (700), `#D9944A` at 0.8
- Terminal: JetBrains Mono, 10px, `#94A3B8` / `#4ADE80`
- Bottom label: Inter, 16px, `#D9944A` at 0.6, centered

### Easing
- Wall appear: `easeOut(back)` over 10 frames — quick spring
- Counter increment: `easeOut(expo)` over 5 frames — snap
- Liquid ripple: `easeOut(sine)` over 10 frames
- Terminal scroll: linear, accelerating
- Final hold glow: `easeInOut(sine)` on 30-frame cycle

## Narration Sync
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."

Segment: `part3_mold_has_three_parts_012`

- **1:20** ("ratchet effect"): Walls begin rapid accumulation
- **1:26** ("Tests only accumulate"): Counter climbing, mold more precise
- **1:31** ("constrains all future generations"): All walls glowing, hold

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={40} color="#1E293B" opacity={0.05} />

    {/* Evolving mold */}
    <MoldOutline cx={960} cy={480}>
      {WALL_ADDITIONS.map((wall, i) => (
        <Sequence from={wall.frame} key={wall.id}>
          <NewWall position={wall.pos} color="#D9944A"
            flashOpacity={0.8} settleOpacity={0.6}
            materializeDuration={10} />
        </Sequence>
      ))}
    </MoldOutline>

    {/* Wall counter */}
    <WallCounter x={1700} y={80}
      label="WALLS:" labelFont="Inter" labelSize={12}
      numberFont="JetBrains Mono" numberSize={36}
      color="#D9944A"
      keyframes={[
        { frame: 0, count: 6 },
        { frame: 30, count: 7 },
        { frame: 60, count: 8 },
        { frame: 120, count: 11 },
        { frame: 240, count: 15 },
        { frame: 330, count: 20 }
      ]} />

    {/* Terminal with scrolling tests */}
    <Sequence from={0}>
      <TerminalPanel x={1350} y={750} width={400} height={180}>
        <ScrollingTestOutput
          tests={TEST_LIST}
          checkColor="#4ADE80"
          textColor="#94A3B8"
          accelerate />
      </TerminalPanel>
    </Sequence>

    {/* Bottom label */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="Tests only accumulate. The mold only gets more precise."
          font="Inter" size={16} color="#D9944A" opacity={0.6}
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
  "diagramId": "ratchet_timelapse",
  "wallProgression": [6, 7, 8, 11, 15, 20],
  "wallColor": "#D9944A",
  "terminalCommand": "pdd test",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part3_mold_has_three_parts_012"]
}
```

---
