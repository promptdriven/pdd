[Remotion] Regeneration Infographic — Prompt Size vs Code Size with U-Curve

# Section 1.11: Regeneration Infographic — Prompt Efficiency & Defect U-Curve

**Tool:** Remotion
**Duration:** ~25s
**Timestamp:** 5:45 - 6:10

## Visual Description
A two-part animated infographic overlay. Part A shows a "compression ratio" visualization: a small document icon labeled "Prompt (~50 lines)" on the left connected by an expanding arrow to a large document icon labeled "Generated Module (~250-500 lines)" on the right, with "5-10x expansion" labeled on the arrow. Part B, appearing below, shows a U-curve chart plotting "Defect Rate" (Y) against "Module Size" (X), with the sweet spot at ~250 lines highlighted with a green marker. The MIT citation "89% accuracy improvement with NL context" appears as a callout badge.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Part A region: (200, 120) to (1720, 440) — top half
- Part B region: (300, 480) to (1620, 920) — bottom half

### Chart/Visual Elements

**Part A — Compression Ratio:**
- Small doc icon: (300, 260), 80x100px, #3B82F6 fill, rounded rectangle
  - Label below: "Prompt" in blue, "~50 lines" in muted
- Expanding arrow: horizontal, from (420, 260) to (1300, 260)
  - Arrow starts thin (4px) and expands to thick (24px) — visual growth metaphor
  - Gradient: #3B82F6 → #22C55E
  - Label above arrow: "5-10x expansion"
- Large doc icon: (1400, 200), 200x220px, #22C55E fill, rounded rectangle with code-line decorations
  - Label below: "Generated Module" in green, "~250-500 lines" in muted

**Part B — Defect U-Curve:**
- X-axis: "Module Size (lines)" — range 0 to 1000+
- Y-axis: "Defect Rate" — relative scale
- U-curve: smooth quadratic curve, high at left (tiny modules), dips at ~250, rises at right (large modules)
  - Curve color: #F59E0B (amber), 3px stroke
  - Fill below curve: subtle amber gradient at 10% opacity
- Sweet spot marker: vertical dashed line at x=250, green circle on curve
  - Label: "~250 lines" with downward arrow, #22C55E
  - Badge: "Sweet spot" in green pill shape
- Danger zones: left and right edges tinted faintly red

**Callout badge:** "89% accuracy with NL context — MIT, 2024"
- Position: top-right corner, (1300, 130)
- Style: pill badge, #22C55E background at 20%, green border

### Animation Sequence
1. **Frame 0-30 (0-1s):** Part A — small doc icon fades in with scale 0.8→1.0.
2. **Frame 20-60 (0.67-2s):** Expanding arrow draws from left to right, growing in thickness.
3. **Frame 50-80 (1.67-2.67s):** Large doc icon fades in with scale 0.8→1.0. "5-10x" label appears.
4. **Frame 70-90 (2.33-3s):** "Prompt ~50 lines" and "Generated Module ~250-500 lines" labels fade in.
5. **Frame 100-130 (3.33-4.33s):** Part B — U-curve axes fade in.
6. **Frame 130-200 (4.33-6.67s):** U-curve draws from left to right — SVG path animation.
7. **Frame 190-220 (6.33-7.33s):** Sweet spot marker appears — green dot with spring animation, dashed line, "~250 lines" label.
8. **Frame 210-240 (7-8s):** MIT callout badge slides in from right.
9. **Frame 240-750 (8-25s):** Hold.

### Typography
- Doc labels: Inter SemiBold, 22px, matching element color
- Size labels: Inter Regular, 18px, #94A3B8
- Arrow label: Inter Bold, 28px, #FFFFFF
- Axis labels: Inter Medium, 16px, #94A3B8
- Sweet spot label: Inter Bold, 22px, #22C55E
- Badge text: Inter SemiBold, 16px, #22C55E
- Callout: Inter SemiBold, 18px, #22C55E

### Easing
- Icon scale in: `spring({ damping: 12, stiffness: 180 })`
- Arrow draw: `easeInOutQuad`
- Curve draw: `easeInOutCubic`
- Sweet spot marker: `spring({ damping: 10, stiffness: 200 })`
- Badge slide: `easeOutCubic`

## Narration Sync
> "Prompts are one-fifth to one-tenth the size of the code they produce. MIT study: natural language context improved code generation accuracy 89 percent. 250-line modules had the lowest defect rates — a U-curve."

Part A appears as "prompts are one-fifth to one-tenth" is spoken. The U-curve draws as "lowest defect rates — a U-curve" is narrated. The MIT badge appears with the citation.

## Code Structure (Remotion)
```typescript
<Sequence from={REGEN_INFOGRAPHIC_START} durationInFrames={750}>
  <AbsoluteFill>
    {/* Part A — Compression ratio */}
    <Sequence from={0} durationInFrames={100}>
      <DocIcon
        position={[300, 260]} size="small" color="#3B82F6"
        label="Prompt" sublabel="~50 lines"
        scale={spring({ frame, fps: 30, config: { damping: 12, stiffness: 180 } })}
      />
    </Sequence>

    <Sequence from={20} durationInFrames={40}>
      <ExpandingArrow
        from={[420, 260]} to={[1300, 260]}
        startWidth={4} endWidth={24}
        gradient={['#3B82F6', '#22C55E']}
        progress={interpolate(frame, [0, 40], [0, 1], { easing: Easing.inOut(Easing.quad) })}
        label="5-10x expansion"
      />
    </Sequence>

    <Sequence from={50} durationInFrames={700}>
      <DocIcon
        position={[1400, 200]} size="large" color="#22C55E"
        label="Generated Module" sublabel="~250-500 lines"
        scale={spring({ frame: frame - 50, fps: 30, config: { damping: 12, stiffness: 180 } })}
      />
    </Sequence>

    {/* Part B — Defect U-curve */}
    <Sequence from={100} durationInFrames={650}>
      <ChartAxes
        xLabel="Module Size (lines)" yLabel="Defect Rate"
        opacity={interpolate(frame, [0, 30], [0, 1])}
      />
      <Sequence from={30}>
        <UCurve
          drawProgress={interpolate(frame, [0, 70], [0, 1], { easing: Easing.inOut(Easing.cubic) })}
          stroke="#F59E0B"
          fillOpacity={0.1}
        />
      </Sequence>
      <Sequence from={90}>
        <SweetSpotMarker
          x={250}
          label="~250 lines"
          color="#22C55E"
          scale={spring({ frame, fps: 30, config: { damping: 10, stiffness: 200 } })}
        />
      </Sequence>
    </Sequence>

    {/* MIT callout badge */}
    <Sequence from={210} durationInFrames={540}>
      <CalloutBadge
        text="89% accuracy with NL context — MIT, 2024"
        color="#22C55E"
        style={{
          transform: `translateX(${interpolate(frame, [0, 30], [100, 0])}px)`,
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
  "compression_ratio": {
    "prompt_size": "~50 lines",
    "module_size": "~250-500 lines",
    "expansion_factor": "5-10x"
  },
  "u_curve": {
    "x_axis": "Module Size (lines)",
    "y_axis": "Defect Rate",
    "sweet_spot": {"x": 250, "label": "~250 lines"},
    "curve_points": [
      {"x": 10, "y": 0.85},
      {"x": 50, "y": 0.55},
      {"x": 100, "y": 0.30},
      {"x": 200, "y": 0.12},
      {"x": 250, "y": 0.08},
      {"x": 300, "y": 0.10},
      {"x": 500, "y": 0.35},
      {"x": 750, "y": 0.60},
      {"x": 1000, "y": 0.82}
    ]
  },
  "mit_citation": "89% accuracy with NL context — MIT, 2024",
  "totalFrames": 750,
  "fps": 30
}
```

---
