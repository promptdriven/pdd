[Remotion]

# Section 5.7: Economics Crossing Callback — The Chart Returns

**Tool:** Remotion
**Duration:** ~10s (300 frames @ 30fps)
**Timestamp:** 22:10 - 22:20

## Visual Description

The sock economics chart from Part 1 (Section 1.2) returns — a full-circle narrative callback. The familiar two-line chart (labor cost rising amber, sock cost falling blue) reappears, but this time the crossing point pulses with new significance. Then the chart morphs: the X-axis labels transform from "1950-2020" to "2020-2030", the "Labor cost" line relabels to "Patching cost", and "Sock cost" relabels to "Generation cost." The crossing point label transforms from "The Threshold" to "Now."

The transformation is smooth and deliberate — the viewer recognizes the chart, then realizes the parallel. The same economics that made sock-darning irrational are now making code-patching irrational. On the final beat, a darning needle icon appears at the post-crossing region with a thin strikethrough, and the narrator delivers the punchline.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: horizontal at $10 intervals, `#1E293B` at 0.06; vertical at decade markers, `#1E293B` at 0.06

### Chart/Visual Elements

#### Initial State — Sock Economics Chart (callback from 1.2)
- Axes, grid, and both lines exactly as in Section 1.2
- Amber line: "Labor cost (per hour)" rising from $2 to $25
- Blue line: "Sock cost" falling from $8 to $0.50
- Crossing point at ~1962 with "The Threshold" label
- Shaded areas: green pre-crossing, red post-crossing

#### Morph Target — Code Economics Chart
- Same visual structure, labels morph:
  - X-axis: "1950...2020" → "2020...2030"
  - Amber line label: "Labor cost (per hour)" → "Patching cost (per fix)"
  - Blue line label: "Sock cost" → "Generation cost"
  - Crossing label: "The Threshold" → "Now"
- Crossing point shifts from ~1962 position to ~2024 position
- Post-crossing area relabels from "Darning irrational" to "Patching irrational"

#### Crossing Point (enhanced)
- Pulsing circle: 14px radius, `#E2E8F0` at 0.9, 3px stroke
- Glow: 24px Gaussian blur, `#E2E8F0` at 0.2 — brighter than Part 1
- Pulse cycle: scale 1.0 → 1.3 → 1.0 over 30 frames, repeating

#### Darning Needle Strikethrough
- Position: in the post-crossing red zone, (1400, 600)
- Needle icon: simple diagonal line with eye loop, `#94A3B8` at 0.4
- Strikethrough: thin diagonal line through needle, `#EF4444` at 0.5
- Appears on the punchline "darning socks"

### Animation Sequence
1. **Frame 0-30 (0-1s):** Sock economics chart fades in — instantly recognizable from Part 1. The viewer has a moment of "I've seen this before."
2. **Frame 30-60 (1-2s):** Crossing point begins pulsing with enhanced glow. Drawing attention.
3. **Frame 60-150 (2-5s):** Morph sequence. Labels smoothly transform:
   - X-axis decades slide and morph into "2020...2030"
   - "Labor cost" text morphs letter-by-letter to "Patching cost"
   - "Sock cost" morphs to "Generation cost"
   - "The Threshold" morphs to "Now"
   - Crossing point position slides to the "2024" region
4. **Frame 150-210 (5-7s):** Post-crossing area relabels. The parallel is complete. The viewer sees: the same chart, the same economics, a different domain.
5. **Frame 210-240 (7-8s):** Darning needle icon with strikethrough appears in the post-crossing zone. The punchline visual.
6. **Frame 240-300 (8-10s):** Hold. Crossing point continues pulsing. The full-circle moment lands.

### Typography
- Axis labels: Inter, 12px, `#64748B` at 0.5
- Line labels: Inter, 13px, respective colors at 0.7
- "Now" label: Inter, 18px, bold (700), `#E2E8F0`
- Morph transition: letter-by-letter interpolation, 2 frames per character

### Easing
- Chart fade-in: `easeOut(quad)` over 20 frames
- Crossing pulse: `easeInOut(sine)` on 30-frame cycle
- Label morph: `easeInOut(cubic)` over 60 frames per label
- Crossing position slide: `easeInOut(cubic)` over 60 frames
- Needle appear: `easeOut(back(1.3))` scale 0→1, 15 frames
- Strikethrough draw: `easeOut(quad)` over 10 frames

## Narration Sync
> "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."

Segment: `part5_007`

- **22:10** ("But the economics changed"): Sock chart fades in, crossing point pulses
- **22:13** ("And when economics change"): Morph begins — labels transform
- **22:16** ("behavior that was rational"): Morph completes — "Now" label visible
- **22:19** ("becomes... darning socks"): Needle strikethrough appears, punchline lands

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={300}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Callback chart — sock economics from Part 1 */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <SockEconomicsChart
          ref={chartRef}
          xRange={[1950, 2020]} yRange={[0, 30]}
          laborData={laborCostData} sockData={sockCostData}
          crossingYear={1962}
          crossingLabel="The Threshold"
          showShadedAreas
        />
      </FadeIn>
    </Sequence>

    {/* Enhanced crossing point pulse */}
    <Sequence from={30}>
      <PulsingHighlight
        position={crossingPoint} radius={14}
        color="#E2E8F0" glowRadius={24} glowOpacity={0.2}
        pulseCycle={30} pulseScale={[1.0, 1.3]}
      />
    </Sequence>

    {/* Morph: sock economics → code economics */}
    <Sequence from={60}>
      <ChartMorph
        chartRef={chartRef}
        duration={90}
        morphs={[
          { target: 'xLabels', to: ['2020','2022','2024','2026','2028','2030'] },
          { target: 'line1Label', to: 'Patching cost (per fix)' },
          { target: 'line2Label', to: 'Generation cost' },
          { target: 'crossingLabel', to: 'Now' },
          { target: 'crossingPosition', to: 2024 },
          { target: 'postCrossingLabel', to: 'Patching irrational' }
        ]}
      />
    </Sequence>

    {/* Darning needle strikethrough */}
    <Sequence from={210}>
      <ScaleIn easing="easeOut(back(1.3))" duration={15}>
        <DarningNeedle position={[1400, 600]}
          color="#94A3B8" opacity={0.4} />
      </ScaleIn>
      <Sequence from={10}>
        <DrawLine from={[1380, 620]} to={[1420, 580]}
          color="#EF4444" opacity={0.5} width={2}
          drawDuration={10} />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "economics_crossing_callback",
  "callback_from": "sock_economics",
  "morphSequence": {
    "initial": {
      "xRange": [1950, 2020],
      "line1": { "label": "Labor cost (per hour)", "color": "#D9944A" },
      "line2": { "label": "Sock cost", "color": "#4A90D9" },
      "crossingYear": 1962,
      "crossingLabel": "The Threshold"
    },
    "final": {
      "xRange": [2020, 2030],
      "line1": { "label": "Patching cost (per fix)", "color": "#D9944A" },
      "line2": { "label": "Generation cost", "color": "#4A90D9" },
      "crossingYear": 2024,
      "crossingLabel": "Now"
    }
  },
  "punchlineIcon": {
    "type": "darning_needle_strikethrough",
    "position": [1400, 600]
  },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part5_007"]
}
```

---
