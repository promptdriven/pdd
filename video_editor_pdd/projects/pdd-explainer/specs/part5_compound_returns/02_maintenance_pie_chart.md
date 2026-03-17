[Remotion]

# Section 5.2: Maintenance Pie Chart — Where the Money Goes

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 21:04 - 21:18

## Visual Description

An animated donut chart materializes to reveal a stark economic truth: 80-90% of software cost is maintenance, not initial development. The chart draws itself clockwise — a thin sliver of blue (#4A90D9) fills "Initial Development: 10-20%", then the massive amber (#D9944A) segment fills the remaining "Maintenance: 80-90%". The disproportion is immediately visceral.

After the chart completes, two research callout cards float in beside it — one for McKinsey (+40% maintenance cost with high tech debt) and one for Stripe (developers waste 33% of work week on debt). These ground the abstract pie chart in credible, specific numbers. The callouts are styled as semi-transparent annotation cards with source citations at reduced opacity.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0F172A` (dark navy)
- Grid lines: none (clean presentation)

### Chart/Visual Elements

#### Donut Chart
- Center: (960, 500)
- Outer radius: 220px
- Inner radius: 120px (donut hole)
- Stroke: 2px `#1E293B` border between segments

#### Segment 1 — Initial Development
- Angle: 36°-72° (10-20% of circle), starting from 12 o'clock
- Color: `#4A90D9` (cool blue)
- Label: "Initial Development" — Inter, 14px, `#4A90D9` at 0.7, with leader line
- Value: "10-20%" — Inter, 20px, bold (700), `#4A90D9`

#### Segment 2 — Maintenance
- Angle: 288°-324° (80-90% of circle)
- Color: `#D9944A` (warm amber)
- Label: "Maintenance" — Inter, 14px, `#D9944A` at 0.7, with leader line
- Value: "80-90%" — Inter, 28px, bold (700), `#D9944A`

#### Donut Center Text
- "SOFTWARE" — Inter, 11px, `#64748B` at 0.4, letter-spacing 3px
- "COST" — Inter, 11px, `#64748B` at 0.4, letter-spacing 3px
- Positioned in donut hole, stacked

#### Research Callout 1 — McKinsey
- Position: (1400, 380), 320x100px card
- Background: `#1E293B` at 0.4, rounded 8px, 1px `#334155` at 0.2 border
- Icon: small bar chart glyph, `#D9944A` at 0.5
- Text: "+40% maintenance cost" — Inter, 16px, semi-bold (600), `#E2E8F0`
- Subtext: "with high technical debt" — Inter, 11px, `#94A3B8` at 0.5
- Source: "McKinsey Digital, 2024" — Inter, 9px, `#64748B` at 0.3

#### Research Callout 2 — Stripe
- Position: (1400, 520), 320x100px card
- Background: `#1E293B` at 0.4, rounded 8px, 1px `#334155` at 0.2 border
- Icon: clock glyph, `#D9944A` at 0.5
- Text: "33% of work week" — Inter, 16px, semi-bold (600), `#E2E8F0`
- Subtext: "spent on technical debt" — Inter, 11px, `#94A3B8` at 0.5
- Source: "Stripe Developer Coefficient, 2018" — Inter, 9px, `#64748B` at 0.3

### Animation Sequence
1. **Frame 0-30 (0-1s):** Donut ring outline fades in (empty circle). Center text appears.
2. **Frame 30-60 (1-2s):** Blue segment draws clockwise from 12 o'clock — the small "Initial Development" slice. Label and value appear.
3. **Frame 60-150 (2-5s):** Amber segment draws clockwise, filling the remaining massive portion. The visual weight is overwhelming. "80-90%" value scales up with emphasis. Label appears.
4. **Frame 150-210 (5-7s):** Hold on completed chart. The 80-90% dominance is self-evident.
5. **Frame 210-270 (7-9s):** McKinsey callout card slides in from right with subtle fade. "+40%" text pulses briefly.
6. **Frame 270-330 (9-11s):** Stripe callout card slides in below McKinsey card. "33%" text pulses briefly.
7. **Frame 330-420 (11-14s):** Hold on complete layout. Both callouts and chart visible.

### Typography
- Segment labels: Inter, 14px, respective colors at 0.7
- Segment values: Inter, 20-28px, bold (700), respective colors
- Center text: Inter, 11px, `#64748B` at 0.4, letter-spacing 3px
- Callout main: Inter, 16px, semi-bold (600), `#E2E8F0`
- Callout sub: Inter, 11px, `#94A3B8` at 0.5
- Callout source: Inter, 9px, `#64748B` at 0.3

### Easing
- Donut ring fade: `easeOut(quad)` over 20 frames
- Blue segment draw: `easeInOut(cubic)` over 30 frames
- Amber segment draw: `easeInOut(cubic)` over 90 frames
- Value scale emphasis: `easeOut(back(1.3))` over 15 frames
- Callout slide-in: `easeOut(cubic)` from x+30, 25 frames
- Callout pulse: `easeInOut(sine)` scale 1.0→1.05→1.0, 20 frames

## Narration Sync
> "Eighty to ninety percent of software cost isn't building the initial system. It's maintaining it. McKinsey found organizations with high technical debt spend forty percent more on maintenance. Stripe measured developers wasting a third of their work week on debt alone."

Segment: `part5_002`

- **21:04** ("Eighty to ninety percent"): Donut chart begins drawing
- **21:08** ("isn't building the initial system"): Blue segment visible, amber filling
- **21:10** ("It's maintaining it"): Amber segment completes, 80-90% dominates
- **21:12** ("McKinsey found"): McKinsey callout slides in
- **21:15** ("Stripe measured"): Stripe callout slides in

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Donut chart ring */}
    <Sequence from={0}>
      <DonutRing center={[960, 500]} outerR={220} innerR={120}
        borderColor="#1E293B" fadeIn={20} />
      <FadeIn duration={20}>
        <Text text="SOFTWARE" font="Inter" size={11}
          color="#64748B" opacity={0.4} letterSpacing={3}
          x={960} y={490} align="center" />
        <Text text="COST" font="Inter" size={11}
          color="#64748B" opacity={0.4} letterSpacing={3}
          x={960} y={510} align="center" />
      </FadeIn>
    </Sequence>

    {/* Blue segment — Initial Development */}
    <Sequence from={30}>
      <DonutSegment
        center={[960, 500]} outerR={220} innerR={120}
        startAngle={0} endAngle={54}
        color="#4A90D9" drawDuration={30}
        label="Initial Development" value="10-20%"
        labelSize={14} valueSize={20}
      />
    </Sequence>

    {/* Amber segment — Maintenance */}
    <Sequence from={60}>
      <DonutSegment
        center={[960, 500]} outerR={220} innerR={120}
        startAngle={54} endAngle={360}
        color="#D9944A" drawDuration={90}
        label="Maintenance" value="80-90%"
        labelSize={14} valueSize={28}
        valueEmphasis={{ easing: 'easeOut(back(1.3))', duration: 15 }}
      />
    </Sequence>

    {/* Research callout — McKinsey */}
    <Sequence from={210}>
      <SlideIn direction="right" distance={30} duration={25}>
        <ResearchCallout
          position={[1400, 380]} width={320}
          icon="bar_chart" iconColor="#D9944A"
          mainText="+40% maintenance cost"
          subText="with high technical debt"
          source="McKinsey Digital, 2024"
        />
      </SlideIn>
    </Sequence>

    {/* Research callout — Stripe */}
    <Sequence from={270}>
      <SlideIn direction="right" distance={30} duration={25}>
        <ResearchCallout
          position={[1400, 520]} width={320}
          icon="clock" iconColor="#D9944A"
          mainText="33% of work week"
          subText="spent on technical debt"
          source="Stripe Developer Coefficient, 2018"
        />
      </SlideIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_chart",
  "chartId": "maintenance_pie",
  "chartType": "donut",
  "segments": [
    {
      "label": "Initial Development",
      "percentage": [10, 20],
      "color": "#4A90D9"
    },
    {
      "label": "Maintenance",
      "percentage": [80, 90],
      "color": "#D9944A"
    }
  ],
  "researchCallouts": [
    {
      "source": "McKinsey Digital, 2024",
      "stat": "+40% maintenance cost",
      "context": "organizations with high technical debt"
    },
    {
      "source": "Stripe Developer Coefficient, 2018",
      "stat": "33% of work week",
      "context": "spent on technical debt"
    }
  ],
  "backgroundColor": "#0F172A",
  "narrationSegments": ["part5_002"]
}
```

---
