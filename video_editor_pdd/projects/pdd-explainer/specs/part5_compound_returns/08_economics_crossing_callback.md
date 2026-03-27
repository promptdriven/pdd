[Remotion]

# Section 5.8: Economics Crossing Callback — "The Economics Changed"

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 1:28 - 1:38

## Visual Description

Return to the code cost chart from Part 1 (spec 1.13). The chart re-establishes with all three lines visible: blue "cost to generate" (now well below), amber solid "immediate patch", and amber dashed "total cost with debt". The crossing point where generation became cheaper than patching is highlighted.

The crossing point pulses again — a radial glow brightening and fading — calling back to the "We are here" moment. But this time, the context has changed. The narration reframes the crossing not as a data point but as a phase transition: "the economics changed."

A subtle text overlay appears: "Behavior that was rational becomes... darning socks." — connecting the sock metaphor full circle to the code economics.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: Horizontal at 150px intervals, `#1E293B` at 0.08

### Chart/Visual Elements

#### Base Chart (from Part 1, spec 1.3/1.13)
- All three lines at their final positions:
  - Generate (blue, `#4A90D9`, 3px) — well below both amber lines
  - Immediate patch (amber solid, `#D9944A`, 3px) — moderate
  - Total cost with debt (amber dashed, `#D9944A`, 2.5px) — near top
- Shaded debt area between amber lines: `#D9944A` at 0.12
- Date markers dimmed: `#64748B` at 0.3

#### Crossing Point Pulse
- Position: where blue line crossed below amber solid (from spec 1.13)
- Radial glow: `#FFFFFF` at 0.2 → 0.05, 25px radius, pulsing
- "We are here." label: still visible, dimmed to `#E2E8F0` at 0.6

#### Reframe Text
- "The economics changed." — Inter, 22px, bold (700), `#E2E8F0`, centered at y: 880
- Subtle underline glow: `#4A90D9` at 0.1

### Animation Sequence
1. **Frame 0-30 (0-1s):** Chart fades in — all elements at final positions from Part 1.
2. **Frame 30-90 (1-3s):** Crossing point begins pulsing — radial glow brightens and fades on a 30-frame cycle.
3. **Frame 90-150 (3-5s):** "We are here." label subtly re-emphasizes. Second pulse — brighter.
4. **Frame 150-210 (5-7s):** "The economics changed." text fades in below chart.
5. **Frame 210-270 (7-9s):** Hold. Chart and text visible. The crossing point continues pulsing.
6. **Frame 270-300 (9-10s):** Chart fades out, preparing for the quote card.

### Typography
- "We are here.": Inter, 24px, bold (700), `#E2E8F0` at 0.6
- "The economics changed.": Inter, 22px, bold (700), `#E2E8F0`
- All chart labels dimmed to 0.4 opacity

### Easing
- Chart fade-in: `easeOut(quad)` over 30 frames
- Crossing pulse: `easeInOut(sine)` on 30-frame cycle, glow opacity 0.05-0.2
- Reframe text: `easeOut(quad)` over 30 frames
- Chart fade-out: `easeIn(quad)` over 30 frames

## Narration Sync
> "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."

Segment: `part5_compound_returns_006`

- **87.76s** (seg 006): Chart fades in — "But the economics changed"
- **90.00s**: Crossing point pulses — "And when economics change"
- **93.00s**: Reframe text — "behavior that was rational becomes..."
- **95.00s**: Beat — "...darning socks"
- **97.36s** (seg 006 ends): Chart begins fading out

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Base chart callback */}
    <Sequence from={0}>
      <FadeIn duration={30}>
        <CodeCostChartFull dimmed={true} dimOpacity={0.4} />
      </FadeIn>
    </Sequence>

    {/* Crossing point pulse */}
    <Sequence from={30}>
      <PulsingGlow
        position={crossingPoint}
        color="#FFFFFF"
        radius={25}
        minOpacity={0.05} maxOpacity={0.2}
        cycleFrames={30}
      />
    </Sequence>

    {/* "We are here" label — dimmed */}
    <Sequence from={30}>
      <Text text="We are here." font="Inter" size={24}
        weight={700} color="#E2E8F0" opacity={0.6}
        x={crossingPoint.x + 40} y={crossingPoint.y + 20} />
    </Sequence>

    {/* Reframe text */}
    <Sequence from={150}>
      <FadeIn duration={30}>
        <Text text="The economics changed."
          font="Inter" size={22} weight={700}
          color="#E2E8F0" x={960} y={880} align="center" />
        <GlowUnderline
          x={860} y={905} width={200}
          color="#4A90D9" opacity={0.1} />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={270}>
      <FadeOut duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "chart_callback",
  "chartRef": "code_cost_generate_vs_patch",
  "sourceSpec": "part1_economics/13_crossing_lines_moment",
  "crossingPoint": {
    "id": "generate_crosses_immediate",
    "year": 2025.6,
    "pulse": true
  },
  "reframeText": "The economics changed.",
  "narrationSegments": ["part5_compound_returns_006"]
}
```

---
