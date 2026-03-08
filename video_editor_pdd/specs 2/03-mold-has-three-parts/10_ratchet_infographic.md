[Remotion] Ratchet Effect Infographic — Test Accumulation Timeline

# Section 3.9: Ratchet Effect Infographic

**Tool:** Remotion
**Duration:** ~12s
**Timestamp:** 1:40 - 1:52

## Visual Description
An animated infographic showing the ratchet effect of test accumulation over time. A horizontal timeline runs across the lower third, with vertical bars rising upward from it. Each bar represents a test added at a point in time. As bars appear left-to-right, the cumulative "mold precision" line (a stepped line graph above the bars) ratchets upward — it can only go up, never down. A small ratchet pawl icon sits on the line to visually reinforce the one-way mechanism. Key moments on the timeline are labeled: "Gen 1: 3 tests", "Gen 5: 18 tests", "Gen 20: 127 tests." The visual clearly shows exponential test growth and irreversible mold tightening.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo ratchet background
- Chart area: centered, (160, 200) to (1760, 880)

### Chart/Visual Elements
- Timeline axis: horizontal line at y=780, from x=200 to x=1720, white at 30% opacity
- Test bars: vertical rectangles rising from timeline, 8px wide, spaced 20px apart
  - Color: #22C55E (test green) at 70% opacity
  - Heights: proportional to test significance (random 40-200px range)
  - 75 bars total, appearing left-to-right
- Ratchet line: stepped line above bars, connecting bar tops
  - Color: #22C55E at full opacity, 3px stroke
  - Direction: monotonically increasing (never decreases)
  - Glow: 0 0 8px rgba(34, 197, 94, 0.5)
- Pawl icon: small ratchet/lock icon that slides along the line as it advances
  - Color: #FFFFFF, 24px
- Generation labels: milestone markers along timeline
  - "Gen 1: 3 tests" at x=240, arrow pointing to 3rd bar
  - "Gen 5: 18 tests" at x=560, arrow pointing to 18th bar
  - "Gen 20: 127 tests" at x=1600, arrow pointing near end
- Y-axis label: "Mold Precision" rotated vertically at left edge
- Background fill below line: gradient fill from #22C55E at 10% to transparent

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Timeline axis draws in from left — width 0→100%.
2. **Frame 10-20 (0.33-0.67s):** Y-axis label "Mold Precision" fades in.
3. **Frame 15-180 (0.5-6s):** Test bars appear sequentially left-to-right (~1 bar per frame). Ratchet line advances with each bar. Pawl icon slides along the line.
4. **Frame 40-55 (1.33-1.83s):** "Gen 1: 3 tests" label fades in near 3rd bar.
5. **Frame 90-105 (3-3.5s):** "Gen 5: 18 tests" label fades in near 18th bar.
6. **Frame 160-175 (5.33-5.83s):** "Gen 20: 127 tests" label fades in near end.
7. **Frame 180-300 (6-10s):** Hold at full state. Subtle pulse on entire line.
8. **Frame 300-360 (10-12s):** Fade out — opacity 1→0.

### Typography
- Y-axis label: Inter Medium, 18px, #94A3B8, rotated -90 degrees
- Generation labels: Inter SemiBold, 16px, #FFFFFF
- Generation count: Inter Bold, 16px, #22C55E
- Arrow connectors: 1px, #94A3B8

### Easing
- Bar appearance: `easeOutQuad` (quick pop-up)
- Ratchet line: `linear` (steady advancement matching bars)
- Label fades: `easeOutCubic`
- Final fade out: `easeInCubic`

## Narration Sync
> "Every test you write is a ratchet click — the mold gets more precise, and it never goes backward. You're accumulating test capital."

Bars begin appearing rapidly on "every test you write is a ratchet click." Generation labels appear during "you're accumulating test capital."

## Code Structure (Remotion)
```typescript
<Sequence from={RATCHET_START} durationInFrames={360}>
  <AbsoluteFill style={{
    opacity: interpolate(frame, [0, 10, 300, 360], [0, 1, 1, 0]),
  }}>
    {/* Timeline axis */}
    <TimelineAxis
      width={interpolate(frame, [0, 15], [0, 1520], { extrapolateRight: 'clamp' })}
      y={780}
    />

    {/* Y-axis label */}
    <RotatedLabel
      text="Mold Precision"
      opacity={interpolate(frame, [10, 20], [0, 1])}
    />

    {/* Test bars + ratchet line */}
    <RatchetChart
      data={testData}
      visibleBars={Math.min(75, Math.max(0, Math.floor(frame - 15)))}
      barColor="#22C55E"
      lineColor="#22C55E"
      lineWidth={3}
    />

    {/* Pawl icon */}
    <PawlIcon
      position={getCurrentLinePosition(frame)}
      size={24}
    />

    {/* Generation milestone labels */}
    <MilestoneLabel
      text="Gen 1: 3 tests"
      x={240}
      opacity={interpolate(frame, [40, 55], [0, 1])}
    />
    <MilestoneLabel
      text="Gen 5: 18 tests"
      x={560}
      opacity={interpolate(frame, [90, 105], [0, 1])}
    />
    <MilestoneLabel
      text="Gen 20: 127 tests"
      x={1600}
      opacity={interpolate(frame, [160, 175], [0, 1])}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "milestones": [
    {"generation": 1, "test_count": 3, "bar_index": 3},
    {"generation": 5, "test_count": 18, "bar_index": 18},
    {"generation": 20, "test_count": 127, "bar_index": 75}
  ],
  "total_bars": 75,
  "bar_width": 8,
  "bar_spacing": 20,
  "chart_area": {"x": 160, "y": 200, "width": 1600, "height": 680},
  "totalFrames": 360,
  "fps": 30
}
```

---
