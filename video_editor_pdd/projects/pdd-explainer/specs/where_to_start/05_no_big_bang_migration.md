[Remotion]

# Section 6.5: No Big Bang Migration — Gradual Stacked Bar

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 23:47 - 23:55

## Visual Description

A horizontal stacked bar chart shows the gradual migration from hand-written code to prompt-driven modules over three time slices. Each bar spans the full width and is divided into two segments: amber (hand-written code) and blue (prompt-driven modules). The proportions shift dramatically across the three rows:

- **Month 1:** 95% amber / 5% blue — you've converted one module
- **Month 3:** 60% amber / 40% blue — steady progress, no disruption
- **Month 6:** 20% amber / 80% blue — the codebase has organically migrated

At the top-left, a crossed-out explosion icon with "No rewrite" label immediately dispels the fear of a big-bang migration. The bars animate sequentially, each sliding its blue segment rightward to claim more territory from amber. The visual rhythm conveys inevitability without urgency — this migration happens naturally as part of normal development.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none

### Chart/Visual Elements

#### "No rewrite" Callout
- Position: (200, 160)
- Explosion icon: 24px, `#EF4444` at 0.4, with 2px diagonal strikethrough `#EF4444` at 0.6
- Text: "No rewrite" — Inter, 14px, semi-bold (600), `#EF4444` at 0.6, 12px right of icon

#### Chart Area
- Left edge: 260, Right edge: 1660, total width: 1400px
- Bar height: 64px, bar spacing: 100px center-to-center
- First bar y-center: 380

#### Bar Row 1 — Month 1
- Time label: "Month 1" — Inter, 14px, semi-bold (600), `#94A3B8` at 0.6, right-aligned at x=240
- Amber segment: 95% of 1400px = 1330px, `#D9944A` at 0.7, rounded left corners 6px
- Blue segment: 5% of 1400px = 70px, `#4A90D9` at 0.7, rounded right corners 6px
- Percentage labels inside segments: "95%" in amber, "5%" in blue — Inter, 12px, bold (700), `#FFFFFF` at 0.8
- Y-center: 380

#### Bar Row 2 — Month 3
- Time label: "Month 3"
- Amber segment: 60% = 840px
- Blue segment: 40% = 560px
- Labels: "60%" in amber, "40%" in blue
- Y-center: 480

#### Bar Row 3 — Month 6
- Time label: "Month 6"
- Amber segment: 20% = 280px
- Blue segment: 80% = 1120px
- Labels: "20%" in amber, "80%" in blue
- Y-center: 580

#### Legend
- Position: centered at (960, 720)
- Amber swatch: 16x16 rounded 3px, `#D9944A`, label "Hand-written code" — Inter, 12px, `#94A3B8` at 0.5
- Blue swatch: 16x16 rounded 3px, `#4A90D9`, label "Prompt-driven modules" — Inter, 12px, `#94A3B8` at 0.5
- 40px gap between items

### Animation Sequence
1. **Frame 0-25 (0-0.83s):** "No rewrite" callout fades in — explosion icon appears, strikethrough draws across it.
2. **Frame 25-50 (0.83-1.67s):** Legend fades in at bottom. Time labels for all three rows fade in.
3. **Frame 50-100 (1.67-3.33s):** Bar 1 animates — amber fills left-to-right, then blue segment pops in at the right edge. "95%" and "5%" labels fade in.
4. **Frame 100-150 (3.33-5s):** Bar 2 animates — amber fills shorter, blue fills larger. The shift is noticeable. Labels appear.
5. **Frame 150-200 (5-6.67s):** Bar 3 animates — amber is now small, blue dominates. "80%" label scales up briefly for emphasis. Labels appear.
6. **Frame 200-240 (6.67-8s):** Hold on complete chart. The 80% blue segment in Month 6 pulses once with a subtle glow.

### Typography
- Time labels: Inter, 14px, semi-bold (600), `#94A3B8` at 0.6
- Percentage labels: Inter, 12px, bold (700), `#FFFFFF` at 0.8
- Legend labels: Inter, 12px, `#94A3B8` at 0.5
- "No rewrite" text: Inter, 14px, semi-bold (600), `#EF4444` at 0.6

### Easing
- Callout fade: `easeOut(quad)` over 20 frames
- Strikethrough draw: `easeInOut(cubic)` over 15 frames
- Amber segment fill: `easeOut(cubic)` over 30 frames
- Blue segment fill: `easeOut(cubic)` over 25 frames
- Label fade: `easeOut(quad)` over 12 frames
- "80%" emphasis: `easeOut(back(1.2))` scale 1.0→1.15→1.0 over 15 frames
- Final glow pulse: `easeInOut(sine)` over 20 frames

## Narration Sync
> "No big bang. No rewrite. Just a gradual migration of where value lives, from code to specification."

Segment: `where_to_start_002`

- **23:47** ("No big bang"): "No rewrite" callout appears with crossed-out explosion
- **23:49** ("No rewrite"): Bar 1 fills — 95% code, 5% prompt
- **23:51** ("Just a gradual migration"): Bar 2 fills — 60/40 shift
- **23:53** ("from code to specification"): Bar 3 fills — 20/80, blue dominates

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* No rewrite callout */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <StrikethroughIcon icon="explosion" iconColor="#EF4444"
          iconOpacity={0.4} strikeColor="#EF4444"
          strikeOpacity={0.6} size={24} x={200} y={160}
          strikeDuration={15} />
        <Text text="No rewrite" font="Inter" size={14}
          weight={600} color="#EF4444" opacity={0.6}
          x={236} y={160} />
      </FadeIn>
    </Sequence>

    {/* Legend */}
    <Sequence from={25}>
      <FadeIn duration={15}>
        <Legend x={960} y={720} items={[
          { color: '#D9944A', label: 'Hand-written code' },
          { color: '#4A90D9', label: 'Prompt-driven modules' }
        ]} font="Inter" size={12} labelColor="#94A3B8" gap={40} />
      </FadeIn>
    </Sequence>

    {/* Time labels */}
    <Sequence from={25}>
      <FadeIn duration={15}>
        {['Month 1','Month 3','Month 6'].map((label, i) => (
          <Text key={label} text={label} font="Inter" size={14}
            weight={600} color="#94A3B8" opacity={0.6}
            x={240} y={380 + i * 100} align="right" />
        ))}
      </FadeIn>
    </Sequence>

    {/* Bar 1 — Month 1: 95/5 */}
    <Sequence from={50}>
      <StackedBar x={260} y={348} width={1400} height={64}
        segments={[
          { percent: 0.95, color: '#D9944A', label: '95%' },
          { percent: 0.05, color: '#4A90D9', label: '5%' }
        ]}
        fillDuration={30} labelDelay={25} borderRadius={6} />
    </Sequence>

    {/* Bar 2 — Month 3: 60/40 */}
    <Sequence from={100}>
      <StackedBar x={260} y={448} width={1400} height={64}
        segments={[
          { percent: 0.60, color: '#D9944A', label: '60%' },
          { percent: 0.40, color: '#4A90D9', label: '40%' }
        ]}
        fillDuration={30} labelDelay={25} borderRadius={6} />
    </Sequence>

    {/* Bar 3 — Month 6: 20/80 */}
    <Sequence from={150}>
      <StackedBar x={260} y={548} width={1400} height={64}
        segments={[
          { percent: 0.20, color: '#D9944A', label: '20%' },
          { percent: 0.80, color: '#4A90D9', label: '80%',
            emphasis: { easing: 'easeOut(back(1.2))', duration: 15 } }
        ]}
        fillDuration={30} labelDelay={25} borderRadius={6} />
    </Sequence>

    {/* Final glow pulse on 80% segment */}
    <Sequence from={200}>
      <GlowPulse target="bar3_segment2" color="#4A90D9"
        blur={12} opacity={0.15} duration={20} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "no_big_bang_migration",
  "chartType": "horizontal_stacked_bar",
  "rows": [
    {
      "label": "Month 1",
      "segments": [
        { "label": "Hand-written code", "percent": 95, "color": "#D9944A" },
        { "label": "Prompt-driven modules", "percent": 5, "color": "#4A90D9" }
      ]
    },
    {
      "label": "Month 3",
      "segments": [
        { "label": "Hand-written code", "percent": 60, "color": "#D9944A" },
        { "label": "Prompt-driven modules", "percent": 40, "color": "#4A90D9" }
      ]
    },
    {
      "label": "Month 6",
      "segments": [
        { "label": "Hand-written code", "percent": 20, "color": "#D9944A" },
        { "label": "Prompt-driven modules", "percent": 80, "color": "#4A90D9" }
      ]
    }
  ],
  "callout": { "text": "No rewrite", "icon": "explosion_strikethrough" },
  "backgroundColor": "#0F172A",
  "narrationSegments": ["where_to_start_002"]
}
```

---
