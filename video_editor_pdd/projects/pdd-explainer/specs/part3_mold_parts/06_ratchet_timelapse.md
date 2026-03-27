[Remotion]

# Section 3.6: Ratchet Effect — Walls Accumulate

**Tool:** Remotion
**Duration:** ~9s (270 frames @ 30fps)
**Timestamp:** 2:08 - 2:17

## Visual Description

A time-lapse of the mold becoming more precise. Starting from the mold with its current walls, new bugs are discovered and new walls materialize in rapid succession. Each cycle takes ~1.5 seconds: red flash → new wall slides in → liquid briefly re-conforms. After 4-5 rapid cycles, the mold interior is densely constrained — many labeled wall segments, very precise cavity shape.

Critically, walls only accumulate. None disappear. A subtle counter in the top-right shows the wall count incrementing: 5 → 6 → 7 → 8 → 9. In the bottom-right corner, a terminal scrolls `pdd test` output with green checkmarks accumulating line by line.

The visual rhythm communicates inevitability: the mold can only become MORE precise over time.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.05

### Chart/Visual Elements

#### Mold (inherited, growing)
- Base walls from previous shots
- New walls slide in from alternating sides (left, right, left, right, bottom)
- Each new wall: `#4A90D9`, same style, labeled with increasingly specific constraints

#### New Wall Labels (rapid succession)
- `handles empty array`
- `timeout at 5s`
- `rejects SQL injection`
- `UTF-8 BOM stripped`
- `max payload 1MB`

#### Wall Counter
- Position: top-right, (1780, 60)
- "WALLS:" label — Inter, 12px, semi-bold (600), `#64748B`
- Count: Inter, 24px, bold (700), `#4A90D9`
- Counter increments on each new wall with a brief scale pulse (1.0 → 1.2 → 1.0)

#### Terminal Scroll
- Position: bottom-right corner, 350px × 100px
- Background: `#1E1E2E` at 0.85
- Lines: `✓ test_null_handling` / `✓ test_empty_string` / etc.
- Green checkmarks: `#A6E3A1`
- New lines scroll up as tests accumulate

### Animation Sequence
1. **Frame 0-54 (0-1.8s):** Cycle 1: Red flash → wall `handles empty array` slides in from left → liquid re-conforms. Counter: 5 → 6.
2. **Frame 54-108 (1.8-3.6s):** Cycle 2: Red flash → wall `timeout at 5s` slides in from right → liquid re-conforms. Counter: 6 → 7.
3. **Frame 108-162 (3.6-5.4s):** Cycle 3: Red flash → wall `rejects SQL injection` from left → re-conform. Counter: 7 → 8.
4. **Frame 162-216 (5.4-7.2s):** Cycle 4: Red flash → wall `UTF-8 BOM stripped` from right → re-conform. Counter: 8 → 9.
5. **Frame 216-270 (7.2-9s):** Hold on dense mold. Terminal shows 9+ green checkmarks. The mold is visually much more constrained than where it started. Subtle glow pulse on all walls.

### Typography
- Wall labels: JetBrains Mono, 11px (smaller to fit more), `#CDD6F4`
- Counter label: Inter, 12px, semi-bold (600), `#64748B`
- Counter number: Inter, 24px, bold (700), `#4A90D9`
- Terminal: JetBrains Mono, 11px, `#A6E3A1`

### Easing
- Wall slide-in: `easeOut(back)` over 20 frames (faster than before)
- Red flash: `easeOut(expo)` over 8 frames
- Counter pulse: `easeOut(quad)` over 10 frames
- Terminal scroll: `easeOut(quad)` per line

## Narration Sync
> "This is the ratchet effect. Tests only accumulate. The mold only gets more precise. Each wall you add constrains all future generations."

Segment: `part3_mold_parts_010`

- **127.62s** (seg 010): Time-lapse begins — "This is the ratchet effect"
- **130.0s**: Walls accumulating rapidly
- **134.0s**: "Each wall you add constrains all future generations"
- **136.94s** (seg 010 ends): Dense mold visible, counter at 9

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={270}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.05} />
    <MoldCrossSection wallsOpacity={0.4} />

    {/* Rapid wall accumulation cycles */}
    {WALL_CYCLES.map((cycle, i) => (
      <Sequence key={i} from={i * 54}>
        <BugFlash duration={8} color="#EF4444" />
        <Sequence from={8}>
          <SlideIn from={cycle.side} distance={150} duration={20}
            easing="easeOut(back)">
            <WallSegment label={cycle.label} color="#4A90D9" />
          </SlideIn>
        </Sequence>
        <Sequence from={28}>
          <LiquidReconform duration={20} />
        </Sequence>
      </Sequence>
    ))}

    {/* Wall counter */}
    <WallCounter
      x={1780} y={60}
      startCount={5}
      increments={[0, 54, 108, 162]}
    />

    {/* Terminal with scrolling test output */}
    <Sequence from={0}>
      <TerminalScroll
        x={1500} y={880} width={350} height={100}
        lines={TEST_LINES}
        scrollRate={54} /* frames per new line */
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "ratchet_timelapse",
  "newWalls": [
    { "label": "handles empty array", "side": "left", "cycle": 1 },
    { "label": "timeout at 5s", "side": "right", "cycle": 2 },
    { "label": "rejects SQL injection", "side": "left", "cycle": 3 },
    { "label": "UTF-8 BOM stripped", "side": "right", "cycle": 4 }
  ],
  "wallCountRange": [5, 9],
  "narrationSegments": ["part3_mold_parts_010"],
  "durationSeconds": 9.0
}
```

---
