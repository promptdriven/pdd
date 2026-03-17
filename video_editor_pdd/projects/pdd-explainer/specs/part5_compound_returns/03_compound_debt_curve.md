[Remotion]

# Section 5.3: Compound Debt Curve — The Math of Accumulation

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 21:18 - 21:30

## Visual Description

The donut chart from the previous beat morphs into a mathematical visualization. An exponential curve draws itself across the screen — labeled with the compound interest formula `Debt × (1 + Rate)^Time`. The curve starts gently but accelerates upward with alarming steepness. Below it, a flat line with a sawtooth pattern represents regeneration cost — each "tooth" shows cost spiking briefly during a regeneration cycle, then resetting to near-zero. The sawtooth resets visualize PDD's key insight: debt doesn't accumulate because code is thrown away and rebuilt.

A CISQ research callout appears: "$1.52 trillion/year" in large type, anchoring the abstract curve to a concrete, staggering number. The callout is positioned in the growing gap between the two lines.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: horizontal at 100px intervals, `#1E293B` at 0.06; vertical at 150px intervals, `#1E293B` at 0.06

### Chart/Visual Elements

#### Axes
- X-axis: "Time" — positioned at y: 800, `#475569` at 0.5, 2px
  - Labels: "Year 1", "Year 3", "Year 5", "Year 7", "Year 10" — Inter, 11px, `#64748B` at 0.4
- Y-axis: "Cost" — positioned at x: 200, `#475569` at 0.5, 2px
  - Labels: "$", "$$", "$$$", "$$$$" (relative scale) — Inter, 11px, `#64748B` at 0.4

#### Exponential Debt Curve
- Color: `#D9944A` (warm amber), 3px stroke
- Path: starts at (200, 720), curves exponentially to (1700, 200)
- Formula label: `Debt × (1 + Rate)^Time` — JetBrains Mono, 14px, `#D9944A` at 0.6, positioned at (1200, 250), following curve angle
- Glow trail: 6px Gaussian blur, `#D9944A` at 0.08, behind the line as it draws

#### Regeneration Sawtooth Line
- Color: `#4A90D9` (cool blue), 2px stroke
- Path: flat baseline at y: 700, with 5 sawtooth peaks rising to y: 650 then resetting
  - Each tooth spans ~300px horizontally, representing one regeneration cycle
  - Peaks are sharp triangles: rise over 30px, fall back over 10px
- Label: "Regeneration cost (resets each cycle)" — Inter, 12px, `#4A90D9` at 0.5, positioned at line endpoint
- Subtle dashed vertical lines at each reset point, `#4A90D9` at 0.08

#### CISQ Callout
- Position: centered in the gap between curves at (1100, 450)
- "$1.52T" — Inter, 48px, bold (700), `#E2E8F0`
- "/year in US tech debt" — Inter, 16px, `#94A3B8` at 0.5
- "CISQ, 2022" — Inter, 10px, `#64748B` at 0.3
- Background: subtle `#1E293B` at 0.2, rounded 12px, padding 20px
- The number sits in the visual gap — the gap *is* the cost

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes draw in. Grid lines fade in. "Time" and "Cost" axis labels appear.
2. **Frame 30-150 (1-5s):** Exponential curve draws from left to right. Starts gentle, then accelerates dramatically upward. Glow trail follows the drawing point. Formula label types in at frame 120.
3. **Frame 90-210 (3-7s):** Sawtooth line begins drawing simultaneously (offset start). Each tooth rises and resets. The contrast with the exponential curve above is stark.
4. **Frame 210-270 (7-9s):** Gap between curves fills with subtle gradient — `#D9944A` at 0.02 on top fading to `#4A90D9` at 0.02 on bottom. CISQ callout fades in within the gap.
5. **Frame 270-300 (9-10s):** "$1.52T" scales up with emphasis bounce. The number anchors the abstraction.
6. **Frame 300-360 (10-12s):** Hold. The exponential vs. flat pattern is self-evident.

### Typography
- Axis labels: Inter, 11px, `#64748B` at 0.4
- Formula: JetBrains Mono, 14px, `#D9944A` at 0.6
- Line labels: Inter, 12px, respective colors at 0.5
- CISQ number: Inter, 48px, bold (700), `#E2E8F0`
- CISQ subtitle: Inter, 16px, `#94A3B8` at 0.5
- CISQ source: Inter, 10px, `#64748B` at 0.3

### Easing
- Axis draw: `easeOut(quad)` over 20 frames
- Exponential curve draw: `easeIn(cubic)` over 120 frames (starts slow, accelerates — matching the math)
- Sawtooth draw: `linear` for flat segments, `easeOut(quad)` for peaks
- Gap gradient fill: `easeOut(quad)` over 30 frames
- CISQ callout fade: `easeOut(quad)` over 20 frames
- "$1.52T" scale emphasis: `easeOut(back(1.4))` over 15 frames

## Narration Sync
> "And those costs compound — literally. Technical debt follows a compound interest curve. CISQ puts the US total at one-point-five-two trillion dollars annually. That's not a metaphor. It's the math of accumulation."

Segment: `part5_003`

- **21:18** ("And those costs compound"): Exponential curve begins drawing
- **21:21** ("Technical debt follows a compound interest curve"): Curve accelerates upward, formula label appears
- **21:24** ("CISQ puts the US total"): CISQ callout begins fading in
- **21:26** ("one-point-five-two trillion"): "$1.52T" scales up with emphasis
- **21:28** ("It's the math of accumulation"): Hold on complete visualization

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Grid and axes */}
    <Sequence from={0}>
      <ChartGrid hSpacing={100} vSpacing={150}
        color="#1E293B" opacity={0.06} />
      <ChartAxes
        xLabel="Time" yLabel="Cost"
        xLabels={['Year 1','Year 3','Year 5','Year 7','Year 10']}
        yLabels={['$','$$','$$$','$$$$']}
        axisColor="#475569" drawDuration={20}
      />
    </Sequence>

    {/* Exponential debt curve */}
    <Sequence from={30}>
      <AnimatedCurve
        data={exponentialDebtData}
        color="#D9944A" width={3}
        drawDuration={120} easing="easeIn(cubic)"
        glow={{ blur: 6, opacity: 0.08 }}
      />
      <Sequence from={90}>
        <TypeWriter
          text="Debt × (1 + Rate)^Time"
          font="JetBrains Mono" size={14}
          color="#D9944A" opacity={0.6}
          position={[1200, 250]}
        />
      </Sequence>
    </Sequence>

    {/* Regeneration sawtooth */}
    <Sequence from={90}>
      <SawtoothLine
        baseline={700} peakHeight={50}
        teeth={5} color="#4A90D9" width={2}
        drawDuration={120}
        label="Regeneration cost (resets each cycle)"
      />
    </Sequence>

    {/* Gap gradient fill */}
    <Sequence from={210}>
      <GradientFill
        topColor="#D9944A" bottomColor="#4A90D9"
        opacity={0.02} fadeDuration={30}
        clipBetween={[exponentialDebtData, sawtoothData]}
      />
    </Sequence>

    {/* CISQ callout */}
    <Sequence from={210}>
      <FadeIn duration={20}>
        <CalloutCard position={[1100, 450]} padding={20}
          bgColor="#1E293B" bgOpacity={0.2} borderRadius={12}>
          <Sequence from={60}>
            <ScaleEmphasis easing="easeOut(back(1.4))" duration={15}>
              <Text text="$1.52T" font="Inter" size={48}
                weight={700} color="#E2E8F0" align="center" />
            </ScaleEmphasis>
          </Sequence>
          <Text text="/year in US tech debt" font="Inter" size={16}
            color="#94A3B8" opacity={0.5} align="center" />
          <Text text="CISQ, 2022" font="Inter" size={10}
            color="#64748B" opacity={0.3} align="center" />
        </CalloutCard>
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "compound_debt_curve",
  "curves": [
    {
      "name": "Technical Debt (exponential)",
      "color": "#D9944A",
      "formula": "Debt × (1 + Rate)^Time",
      "dataPoints": [
        { "x": 1, "y": 1.0 },
        { "x": 2, "y": 1.4 },
        { "x": 3, "y": 2.1 },
        { "x": 5, "y": 4.2 },
        { "x": 7, "y": 8.5 },
        { "x": 10, "y": 24.0 }
      ]
    },
    {
      "name": "Regeneration cost (sawtooth)",
      "color": "#4A90D9",
      "pattern": "sawtooth",
      "baseline": 1.0,
      "peakHeight": 1.5,
      "resetCycles": 5
    }
  ],
  "callout": {
    "stat": "$1.52T",
    "context": "annual US tech debt cost",
    "source": "CISQ, 2022"
  },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part5_003"]
}
```

---
