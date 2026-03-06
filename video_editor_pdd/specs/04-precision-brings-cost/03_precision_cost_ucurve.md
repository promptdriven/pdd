[Remotion] Precision vs Cost U-Curve Chart Overlay

# Section 4.2: Precision vs Cost U-Curve Chart

**Tool:** Remotion
**Duration:** ~30s
**Timestamp:** 0:30 - 1:00

## Visual Description
An animated U-curve chart overlaid on the Veo precision curve background. The X-axis represents "Prompt Precision" from "Vague" (left) to "Over-Specified" (right). The Y-axis represents "Effective Cost" from low (bottom) to high (top). A smooth U-shaped curve draws itself from the left (high cost of vagueness/hallucination), dips to a sweet spot in the center, and rises again on the right (high cost of over-specification). The sweet spot minimum is highlighted with a pulsing amber glow dot and a "Sweet Spot" callout label. Two shaded danger zones on either end are labeled "AI Hallucinates" (left, red tint) and "Writing Code Yourself" (right, amber tint). Grid lines and axis labels fade in first, then the curve draws dramatically.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Chart area: 200px padding left/bottom, 100px padding right/top → chart region (200, 80) to (1820, 880)

### Chart/Visual Elements
- X-axis: "Prompt Precision" — left="Vague" to right="Over-Specified"
- Y-axis: "Effective Cost" — bottom="Low" to top="High"
- U-curve: #3B82F6 stroke, 4px width, smooth quadratic Bezier
  - Left arm: starts at (200, 200), descends to sweet spot
  - Bottom: sweet spot minimum at approximately (960, 750)
  - Right arm: ascends from sweet spot to (1820, 250)
- Sweet spot dot: amber (#F59E0B), 14px circle with pulsing glow ring (30px, opacity 40%→80%)
- Sweet spot label: "Sweet Spot" with upward arrow, positioned below minimum
- Left danger zone: red-tinted rectangle from x=200 to x=500, rgba(239, 68, 68, 0.08)
  - Label: "AI Hallucinates" at bottom, #EF4444
- Right danger zone: amber-tinted rectangle from x=1500 to x=1820, rgba(245, 158, 11, 0.08)
  - Label: "Writing Code Yourself" at bottom, #F59E0B
- Grid lines: horizontal dashed lines at 25%, 50%, 75% of Y range, #334155 at 15% opacity

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in — X and Y axis lines, tick marks, labels. Opacity 0→1.
2. **Frame 20-50 (0.67-1.67s):** Grid lines fade in subtly. Opacity 0→0.15.
3. **Frame 40-70 (1.33-2.33s):** Left danger zone fades in — red tint rectangle and "AI Hallucinates" label.
4. **Frame 60-90 (2-3s):** Right danger zone fades in — amber tint rectangle and "Writing Code Yourself" label.
5. **Frame 70-220 (2.33-7.33s):** U-curve draws from left to right — SVG path dashoffset animation, smooth and dramatic.
6. **Frame 200-240 (6.67-8s):** Sweet spot dot appears — scales 0→1 with spring, glow ring begins pulsing.
7. **Frame 230-260 (7.67-8.67s):** "Sweet Spot" label fades in with upward arrow.
8. **Frame 260-850 (8.67-28.33s):** Hold. Sweet spot glow continues pulsing.
9. **Frame 850-900 (28.33-30s):** Entire chart fades out — opacity 1→0.

### Typography
- Axis labels: Inter Medium, 18px, #94A3B8
- Axis title (X): Inter Medium, 20px, #CBD5E1, centered below X-axis
- Axis title (Y): Inter Medium, 20px, #CBD5E1, rotated 90°, left of Y-axis
- X-axis endpoints: Inter SemiBold, 16px — "Vague" (#EF4444 left), "Over-Specified" (#F59E0B right)
- Danger zone labels: Inter SemiBold, 20px, matching zone color
- Sweet spot label: Inter Bold, 24px, #F59E0B
- Sweet spot sublabel: Inter Medium, 16px, #CBD5E1

### Easing
- Axis fade in: `easeOutCubic`
- Danger zone fade: `easeOutQuad`
- U-curve draw: `easeInOutQuad`
- Sweet spot dot scale: `spring({ damping: 12, stiffness: 200 })`
- Sweet spot glow pulse: sinusoidal, 2s period
- Chart fade out: `easeInCubic`

## Narration Sync
> "There's a sweet spot between vagueness and over-specification. Too little precision — AI hallucinates. Too much — you're writing the code yourself. The U-curve has a minimum."

Axes and grid appear as the narration sets up the framing. The U-curve draws as "sweet spot between vagueness and over-specification" is spoken. Left danger zone highlights on "AI hallucinates." Right danger zone highlights on "writing the code yourself." Sweet spot pulses on "The U-curve has a minimum."

## Code Structure (Remotion)
```typescript
<Sequence from={UCURVE_START} durationInFrames={900}>
  <AbsoluteFill>
    {/* Axes and grid */}
    <Sequence from={0} durationInFrames={50}>
      <ChartAxes
        xLabel="Prompt Precision"
        yLabel="Effective Cost"
        xEndpoints={["Vague", "Over-Specified"]}
        opacity={interpolate(frame, [0, 30], [0, 1])}
        gridOpacity={interpolate(frame, [20, 50], [0, 0.15])}
      />
    </Sequence>

    {/* Left danger zone — AI Hallucinates */}
    <Sequence from={40} durationInFrames={860}>
      <DangerZone
        side="left"
        label="AI Hallucinates"
        color="#EF4444"
        opacity={interpolate(frame, [0, 30, 810, 860], [0, 0.08, 0.08, 0])}
        labelOpacity={interpolate(frame, [0, 30, 810, 860], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* Right danger zone — Writing Code Yourself */}
    <Sequence from={60} durationInFrames={840}>
      <DangerZone
        side="right"
        label="Writing Code Yourself"
        color="#F59E0B"
        opacity={interpolate(frame, [0, 30, 790, 840], [0, 0.08, 0.08, 0])}
        labelOpacity={interpolate(frame, [0, 30, 790, 840], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* U-Curve — draws in */}
    <Sequence from={70} durationInFrames={830}>
      <AnimatedCurve
        data={uCurveData}
        stroke="#3B82F6"
        strokeWidth={4}
        drawProgress={interpolate(frame, [0, 150], [0, 1], {
          easing: Easing.inOut(Easing.quad),
          extrapolateRight: 'clamp',
        })}
        opacity={interpolate(frame, [0, 1, 780, 830], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* Sweet spot dot */}
    <Sequence from={200} durationInFrames={700}>
      <SweetSpotDot
        position={sweetSpotXY}
        dotScale={spring({ frame: frame - 200, fps: 30, config: { damping: 12, stiffness: 200 } })}
        glowOpacity={interpolate(Math.sin(frame * 0.105), [-1, 1], [0.4, 0.8])}
        color="#F59E0B"
      />
      <Sequence from={30}>
        <SweetSpotLabel
          text="Sweet Spot"
          opacity={interpolate(frame, [0, 30], [0, 1], { extrapolateRight: 'clamp' })}
        />
      </Sequence>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "ucurve": {
    "label": "Effective Cost vs Precision",
    "color": "#3B82F6",
    "points": [
      {"x": 0.0, "y": 0.85},
      {"x": 0.1, "y": 0.65},
      {"x": 0.2, "y": 0.45},
      {"x": 0.3, "y": 0.30},
      {"x": 0.4, "y": 0.20},
      {"x": 0.5, "y": 0.15},
      {"x": 0.6, "y": 0.18},
      {"x": 0.7, "y": 0.28},
      {"x": 0.8, "y": 0.45},
      {"x": 0.9, "y": 0.68},
      {"x": 1.0, "y": 0.90}
    ]
  },
  "sweet_spot": {"x": 0.5, "y": 0.15},
  "danger_zones": {
    "left": {"label": "AI Hallucinates", "x_range": [0, 0.2], "color": "#EF4444"},
    "right": {"label": "Writing Code Yourself", "x_range": [0.8, 1.0], "color": "#F59E0B"}
  },
  "chart_frames": 900,
  "fps": 30
}
```

---
