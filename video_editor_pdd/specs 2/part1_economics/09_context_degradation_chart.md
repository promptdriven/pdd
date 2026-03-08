[Remotion] Context Window Capability Loss — Declining Bar Chart

# Section 1.8: Context Degradation Chart — EMNLP Capability Loss

**Tool:** Remotion
**Duration:** ~30s
**Timestamp:** 4:15 - 4:45

## Visual Description
An animated bar chart showing AI capability declining as context window fills. Five vertical bars represent different fill levels (10%, 25%, 50%, 75%, 100%), with each bar shorter than the last. The bars are color-coded from green (high capability) to red (low capability). Each bar animates upward from the baseline sequentially, with a percentage label appearing above each bar. A downward trend line connects the bar tops, drawn after all bars appear. The EMNLP citation "14-85% capability loss" appears as a highlighted callout below the chart.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Chart area: centered, (300, 150) to (1620, 850) — 1320px x 700px

### Chart/Visual Elements
- X-axis: "Context Window Fill Level" — labels: 10%, 25%, 50%, 75%, 100%
- Y-axis: "AI Capability" — 0% to 100%
- Bar widths: 120px each, 60px gap between bars
- Bar A (10% fill): height=95% of chart, color #22C55E (green)
- Bar B (25% fill): height=82% of chart, color #84CC16 (lime)
- Bar C (50% fill): height=58% of chart, color #F59E0B (amber)
- Bar D (75% fill): height=32% of chart, color #F97316 (orange)
- Bar E (100% fill): height=15% of chart, color #EF4444 (red)
- Trend line: dashed, 3px, #FFFFFF at 60% opacity, connecting bar tops
- Callout box: "14-85% capability loss" — positioned below chart, red accent

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in — labels, tick marks. Opacity 0→1.
2. **Frame 30-60 (1-2s):** Bar A grows from baseline — height 0→95%, label "95%" appears above.
3. **Frame 50-80 (1.67-2.67s):** Bar B grows — height 0→82%, label "82%" appears.
4. **Frame 70-100 (2.33-3.33s):** Bar C grows — height 0→58%, label "58%" appears. Amber color signals concern.
5. **Frame 90-120 (3-4s):** Bar D grows — height 0→32%, label "32%" appears.
6. **Frame 110-140 (3.67-4.67s):** Bar E grows — height 0→15%, label "15%" appears. Red signals danger.
7. **Frame 140-180 (4.67-6s):** Trend line draws across bar tops — SVG dashoffset animation.
8. **Frame 180-210 (6-7s):** Callout "14-85% capability loss" slides up from bottom, opacity 0→1.
9. **Frame 210-900 (7-30s):** Hold with subtle bar glow pulsing.

### Typography
- Axis labels: Inter Medium, 18px, #94A3B8
- Axis title: Inter Medium, 20px, #CBD5E1
- Bar value labels: Inter Bold, 28px, matching bar color
- Callout text: Inter Bold, 32px, #EF4444
- Callout source: Inter Regular, 16px, #94A3B8, "EMNLP 2024"

### Easing
- Axis fade: `easeOutCubic`
- Bar growth: `spring({ damping: 12, stiffness: 150 })`
- Label fade: `easeOutQuad`
- Trend line draw: `easeInOutCubic`
- Callout slide: `spring({ damping: 15, stiffness: 180 })`

## Narration Sync
> "EMNLP research showed 14 to 85 percent capability loss as context windows fill."

Bars animate sequentially as the narrator describes degradation. The callout with "14-85%" appears in sync with the citation.

## Code Structure (Remotion)
```typescript
<Sequence from={CONTEXT_CHART_START} durationInFrames={900}>
  <AbsoluteFill>
    {/* Axes */}
    <ChartAxes
      xLabel="Context Window Fill Level"
      yLabel="AI Capability"
      xTicks={['10%', '25%', '50%', '75%', '100%']}
      opacity={interpolate(frame, [0, 30], [0, 1])}
    />

    {/* Bars — staggered growth */}
    {bars.map((bar, i) => (
      <Sequence key={bar.label} from={30 + i * 20} durationInFrames={870 - i * 20}>
        <AnimatedBar
          x={barPositions[i]}
          targetHeight={bar.heightPercent}
          color={bar.color}
          progress={spring({ frame, fps: 30, config: { damping: 12, stiffness: 150 } })}
        />
        <BarLabel
          value={`${bar.capability}%`}
          color={bar.color}
          opacity={interpolate(frame, [20, 30], [0, 1])}
        />
      </Sequence>
    ))}

    {/* Trend line */}
    <Sequence from={140} durationInFrames={40}>
      <TrendLine
        points={barTops}
        drawProgress={interpolate(frame, [0, 40], [0, 1], { easing: Easing.inOut(Easing.cubic) })}
        stroke="#FFFFFF"
        strokeOpacity={0.6}
        strokeWidth={3}
        dashArray="8 6"
      />
    </Sequence>

    {/* Callout */}
    <Sequence from={180} durationInFrames={720}>
      <CalloutBox
        text="14-85% capability loss"
        source="EMNLP 2024"
        color="#EF4444"
        style={{
          transform: `translateY(${interpolate(frame, [0, 30], [40, 0])}px)`,
          opacity: interpolate(frame, [0, 30], [0, 1]),
        }}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "bars": [
    {"fill_level": "10%", "capability": 95, "color": "#22C55E"},
    {"fill_level": "25%", "capability": 82, "color": "#84CC16"},
    {"fill_level": "50%", "capability": 58, "color": "#F59E0B"},
    {"fill_level": "75%", "capability": 32, "color": "#F97316"},
    {"fill_level": "100%", "capability": 15, "color": "#EF4444"}
  ],
  "callout": "14-85% capability loss",
  "source": "EMNLP 2024",
  "chart_region": {"x": 300, "y": 150, "width": 1320, "height": 700},
  "totalFrames": 900,
  "fps": 30
}
```

---
