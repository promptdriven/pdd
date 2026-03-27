[Remotion]

# Section 2.4: Mold Production Counter

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 1:09 - 1:19

## Visual Description

An animated counter overlay on a cinematic background showing injection molded parts ejecting in rapid succession. The mold opens, a perfect plastic part ejects, the mold closes, repeat — each cycle faster than the last. A large counter in the lower-right counts: 1... 10... 100... 1,000... 10,000. The counter accelerates exponentially. Each ejected part is identical — the perfection of the mold reproduced endlessly.

The background is a semi-stylized render of the molding cycle: mold halves open/close in a simple 2D animation while the counter dominates focus. A progress bar beneath the counter fills as the number climbs.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: None

### Chart/Visual Elements

#### Mold Animation (center)
- Simple 2D cross-section: two mold halves (steel gray `#78909C`) open and close
- Plastic part shape: `#D9944A`, ejects upward when mold opens
- Cycle speed: starts at 60 frames/cycle, compresses to 6 frames/cycle

#### Counter (lower-right)
- Large number: JetBrains Mono, 96px, bold, `#E2E8F0`
- Label beneath: "parts produced", Inter, 16px, `#94A3B8` at 0.6
- Counter position: x: 1400, y: 700

#### Progress Bar (beneath counter)
- Width: 300px, height: 4px
- Track: `#1E293B`
- Fill: gradient from `#4A90D9` to `#5AAA6E`

### Animation Sequence
1. **Frame 0-30 (0-1s):** Mold animation begins. First part ejects slowly. Counter: 1.
2. **Frame 30-90 (1-3s):** Cycle accelerates. Counter climbs: 1 → 10 → 50. Parts eject faster.
3. **Frame 90-180 (3-6s):** Rapid-fire ejection. Counter: 50 → 500 → 1,000. Mold animation is a blur.
4. **Frame 180-240 (6-8s):** Counter: 1,000 → 5,000 → 10,000. Progress bar fills.
5. **Frame 240-300 (8-10s):** Counter holds at 10,000+. Parts continue streaming. The scale is the message.

### Typography
- Counter: JetBrains Mono, 96px, bold (700), `#E2E8F0`
- Label: Inter, 16px, regular (400), `#94A3B8` at 0.6

### Easing
- Counter increment: `easeIn(expo)` — starts slow, accelerates dramatically
- Mold cycle speed: `easeIn(quad)` — progressive compression
- Progress bar fill: `easeInOut(cubic)` over full duration
- Part eject: `easeOut(quad)` per cycle

## Narration Sync
> "Make the mold once, produce unlimited identical parts. Refine the mold once, every future part improves automatically."

Segment: `part2_paradigm_shift_006` (tail)

- **69.0s**: Counter begins — first parts eject
- **72.0s**: Counter accelerating — "produce unlimited identical parts"
- **76.0s**: Counter at thousands — "every future part improves automatically"
- **76.34s** (seg 006 ends): Counter holds

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Mold cycle animation */}
    <MoldCycleAnimation
      startSpeed={60} endSpeed={6}
      moldColor="#78909C" partColor="#D9944A"
      easing="easeInQuad"
    />

    {/* Counter */}
    <Sequence from={0}>
      <ExponentialCounter
        start={1} end={10000}
        font="JetBrains Mono" size={96}
        color="#E2E8F0" x={1400} y={700}
        easing="easeInExpo"
      />
      <Text text="parts produced" font="Inter" size={16}
        color="#94A3B8" opacity={0.6}
        x={1400} y={770} align="center" />
    </Sequence>

    {/* Progress bar */}
    <Sequence from={0}>
      <ProgressBar
        width={300} height={4} x={1250} y={800}
        trackColor="#1E293B"
        fillGradient={["#4A90D9", "#5AAA6E"]}
        easing="easeInOutCubic"
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "counter_animation",
  "chartId": "mold_production_counter",
  "counter": {
    "start": 1,
    "end": 10000,
    "milestones": [1, 10, 100, 1000, 10000],
    "easing": "exponential"
  },
  "moldCycle": {
    "startFramesPerCycle": 60,
    "endFramesPerCycle": 6
  },
  "narrationSegments": ["part2_paradigm_shift_006"]
}
```

---
