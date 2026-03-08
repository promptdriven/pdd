[Remotion] Compound Debt Accumulation Chart — Patching vs Generation Curves

# Section 5.5: Compound Debt Accumulation Chart Overlay

**Tool:** Remotion
**Duration:** ~22s
**Timestamp:** 0:28 - 0:50

## Visual Description
An animated dual-line chart overlaid on the Veo compound debt background. The X-axis represents "Time" from "Month 1" to "Month 24". The Y-axis represents "Accumulated Technical Debt" from zero (bottom) to high (top). Two curves draw themselves simultaneously: the red "Patching" line climbs in an accelerating exponential arc — each patch adding residual complexity that compounds. The green "Generation" line stays remarkably flat with small sawtooth resets — each regeneration cycle produces fresh code, resetting debt to near-zero. The area between the two curves fills with a gradient red haze, growing denser as the gap widens. A "Gap compounds" annotation with an arrow appears in the growing space between curves. Grid lines and axis labels fade in first, then both curves draw simultaneously.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay on Veo background
- Chart area: 200px padding left/bottom, 100px padding right/top → chart region (200, 80) to (1820, 880)

### Chart/Visual Elements
- X-axis: "Time" — left="Month 1" to right="Month 24"
- Y-axis: "Accumulated Technical Debt" — bottom="Zero" to top="Critical"
- Patching curve: #EF4444 stroke, 4px width, exponential growth
  - Start: (200, 800) near zero
  - Month 6: (600, 650) modest rise
  - Month 12: (1000, 450) accelerating
  - Month 18: (1400, 250) steep climb
  - Month 24: (1820, 120) near top
- Generation curve: #22C55E stroke, 3px width, flat with sawtooth resets
  - Baseline: y=780 (near zero)
  - Resets every ~100px (4 months) — brief dip to y=800 then return to y=780
  - Never rises above y=720
- Gap fill: linear gradient from rgba(239, 68, 68, 0.04) at left to rgba(239, 68, 68, 0.15) at right
- Gap annotation: "The gap compounds" with downward arrow, positioned at (1200, 400), #FFFFFF
- Patching label: "Patching" in red, positioned at curve end (1820, 120)
- Generation label: "Generation" in green, positioned at curve end (1820, 780)
- Grid lines: horizontal dashed lines at 25%, 50%, 75% of Y range, #334155 at 15% opacity
- Time markers: vertical dashed lines at Month 6, 12, 18, #334155 at 10% opacity

### Animation Sequence
1. **Frame 0-30 (0-1s):** Axes fade in — X and Y axis lines, tick marks, labels. Opacity 0→1.
2. **Frame 20-50 (0.67-1.67s):** Grid lines and time markers fade in subtly. Opacity 0→0.15.
3. **Frame 40-45 (1.33-1.5s):** Curve labels "Patching" and "Generation" appear at origin.
4. **Frame 45-350 (1.5-11.67s):** Both curves draw simultaneously from left to right — SVG path dashoffset animation. Patching climbs; Generation stays flat with sawtooth resets.
5. **Frame 100-350 (3.33-11.67s):** Gap fill fades in progressively as curves diverge — opacity increases from left to right in sync with the drawing.
6. **Frame 300-350 (10-11.67s):** "The gap compounds" annotation fades in with arrow — opacity 0→1.
7. **Frame 350-600 (11.67-20s):** Hold. Full chart visible.
8. **Frame 600-660 (20-22s):** Entire chart fades out — opacity 1→0.

### Typography
- Axis labels: Inter Medium, 18px, #94A3B8
- Axis title (X): Inter Medium, 20px, #CBD5E1, centered below X-axis
- Axis title (Y): Inter Medium, 20px, #CBD5E1, rotated 90°, left of Y-axis
- Curve labels: Inter Bold, 20px — "Patching" (#EF4444), "Generation" (#22C55E)
- Time markers: Inter Regular, 14px, #64748B
- Gap annotation: Inter SemiBold, 28px, #FFFFFF with text shadow 0 2px 8px rgba(0, 0, 0, 0.6)
- Arrow: 2px stroke, #FFFFFF at 80% opacity

### Easing
- Axis fade in: `easeOutCubic`
- Grid fade: `easeOutQuad`
- Both curves draw: `easeInOutQuad` (synchronized)
- Gap fill: linear (matches curve drawing progress)
- Annotation fade: `easeOutCubic`
- Chart fade out: `easeInCubic`

## Narration Sync
> "Patching accumulates debt linearly — each patch adds residual complexity. Generation resets debt each cycle — fresh code, no residue. The gap compounds."

Axes and grid appear as the narration sets up the framing. The patching curve draws upward as "patching accumulates debt linearly" is spoken. The generation curve's flat shape becomes visible during "generation resets debt each cycle." The gap annotation appears on "the gap compounds."

## Code Structure (Remotion)
```typescript
<Sequence from={DEBT_CHART_START} durationInFrames={660}>
  <AbsoluteFill>
    {/* Axes and grid */}
    <Sequence from={0} durationInFrames={50}>
      <ChartAxes
        xLabel="Time"
        yLabel="Accumulated Technical Debt"
        xEndpoints={["Month 1", "Month 24"]}
        yEndpoints={["Zero", "Critical"]}
        opacity={interpolate(frame, [0, 30], [0, 1])}
        gridOpacity={interpolate(frame, [20, 50], [0, 0.15])}
      />
    </Sequence>

    {/* Patching curve — exponential climb */}
    <Sequence from={45} durationInFrames={615}>
      <AnimatedCurve
        data={patchingCurveData}
        stroke="#EF4444"
        strokeWidth={4}
        drawProgress={interpolate(frame, [0, 305], [0, 1], {
          easing: Easing.inOut(Easing.quad),
          extrapolateRight: 'clamp',
        })}
        opacity={interpolate(frame, [0, 1, 555, 615], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* Generation curve — flat with sawtooth resets */}
    <Sequence from={45} durationInFrames={615}>
      <AnimatedCurve
        data={generationCurveData}
        stroke="#22C55E"
        strokeWidth={3}
        drawProgress={interpolate(frame, [0, 305], [0, 1], {
          easing: Easing.inOut(Easing.quad),
          extrapolateRight: 'clamp',
        })}
        opacity={interpolate(frame, [0, 1, 555, 615], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* Gap fill between curves */}
    <Sequence from={100} durationInFrames={560}>
      <GapFill
        topCurve={patchingCurveData}
        bottomCurve={generationCurveData}
        fillColor="rgba(239, 68, 68, 0.12)"
        progress={interpolate(frame, [0, 250], [0, 1], { extrapolateRight: 'clamp' })}
        opacity={interpolate(frame, [0, 1, 500, 560], [0, 1, 1, 0])}
      />
    </Sequence>

    {/* Gap annotation */}
    <Sequence from={300} durationInFrames={360}>
      <Annotation
        text="The gap compounds"
        position={[1200, 400]}
        arrowDirection="down"
        opacity={interpolate(frame, [0, 50, 300, 360], [0, 1, 1, 0])}
      />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "patching_curve": {
    "label": "Patching",
    "color": "#EF4444",
    "points": [
      {"month": 1, "debt": 0.02},
      {"month": 3, "debt": 0.06},
      {"month": 6, "debt": 0.15},
      {"month": 9, "debt": 0.30},
      {"month": 12, "debt": 0.50},
      {"month": 15, "debt": 0.68},
      {"month": 18, "debt": 0.82},
      {"month": 21, "debt": 0.91},
      {"month": 24, "debt": 0.97}
    ]
  },
  "generation_curve": {
    "label": "Generation",
    "color": "#22C55E",
    "points": [
      {"month": 1, "debt": 0.02},
      {"month": 4, "debt": 0.05, "reset": true},
      {"month": 5, "debt": 0.01},
      {"month": 8, "debt": 0.05, "reset": true},
      {"month": 9, "debt": 0.01},
      {"month": 12, "debt": 0.05, "reset": true},
      {"month": 13, "debt": 0.01},
      {"month": 16, "debt": 0.05, "reset": true},
      {"month": 17, "debt": 0.01},
      {"month": 20, "debt": 0.05, "reset": true},
      {"month": 21, "debt": 0.01},
      {"month": 24, "debt": 0.04}
    ]
  },
  "gap_annotation": "The gap compounds",
  "chart_frames": 660,
  "fps": 30
}
```

---
