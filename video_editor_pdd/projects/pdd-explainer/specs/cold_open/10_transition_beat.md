[Remotion]

# Section 0.10: Transition Beat — Accumulated Weight Meter

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:08 - 0:11

## Visual Description
A minimal animated infographic that appears as a lower-third overlay during the second half of the split-screen (beats 3-4). Two horizontal progress bars stack vertically, labeled "Patches Applied" and "Time Spent Repairing." Both bars fill simultaneously from left to right — the top bar in amber (#F59E0B) and the bottom in red (#EF4444) — visualizing the accumulated cost of repair work. Small counters beside each bar tick upward: "2,847 patches" and "1,240 hrs." The bars overshoot their container slightly at the end, implying overflow. This reinforces the visual metaphor before the hard cut to modern day.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9) — lower-third overlay (positioned at y: 780, centered horizontally)
- Overlay container: 600x160px, background #000000 at 70% opacity, border-radius 12px
- This overlays on top of the split-screen composition (spec 01)

### Chart/Visual Elements
- **Bar 1 ("Patches Applied"):**
  - Container: 460x28px, border 1px #333333, border-radius 6px
  - Fill: #F59E0B (amber), animates width 0% → 105% (overshoots container)
  - Counter: "2,847 patches" — number ticks from 0 to 2847
- **Bar 2 ("Time Spent Repairing"):**
  - Container: 460x28px, border 1px #333333, border-radius 6px
  - Fill: #EF4444 (red), animates width 0% → 102%
  - Counter: "1,240 hrs" — number ticks from 0 to 1240
- Labels left-aligned, counters right-aligned

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Overlay container fades in from 0% → 100% opacity
2. **Frame 8-70 (0.27-2.3s):** Both bars fill left-to-right simultaneously. Counters tick up in sync. Bars ease out as they approach 100%.
3. **Frame 70-80 (2.3-2.7s):** Bars overshoot past 100% container width (amber to 105%, red to 102%). Counters settle on final numbers.
4. **Frame 80-90 (2.7-3.0s):** Hold. Subtle pulse on both bars (opacity 1.0 → 0.9 → 1.0) to draw attention.

### Typography
- Labels: Inter Medium, 14px, #AAAAAA
- Counters: JetBrains Mono, 16px, #FFFFFF

### Easing
- Container fade-in: `easeOutQuad`
- Bar fill: `easeOutCubic` (fast start, slow finish — feeling of accumulation)
- Counter tick: `linear` (steady count-up)
- Overshoot: `easeOutBack` (slight bounce past boundary)
- Pulse: `easeInOutSine`

## Narration Sync
> "But here's what your great-grandmother figured out sixty years ago."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={90}>
  {/* Overlay container */}
  <FadeIn durationInFrames={8}>
    <AbsolutePosition x={660} y={780}>
      <OverlayCard width={600} height={160} bgColor="#000000" bgOpacity={0.7} borderRadius={12}>
        {/* Bar 1: Patches */}
        <ProgressBar
          label="Patches Applied"
          fillColor="#F59E0B"
          targetPercent={105}
          counter={{ end: 2847, suffix: " patches" }}
          startFrame={8}
          fillDuration={62}
        />
        {/* Bar 2: Time */}
        <ProgressBar
          label="Time Spent Repairing"
          fillColor="#EF4444"
          targetPercent={102}
          counter={{ end: 1240, suffix: " hrs" }}
          startFrame={8}
          fillDuration={62}
        />
      </OverlayCard>
    </AbsolutePosition>
  </FadeIn>

  {/* Pulse at end */}
  <Sequence from={80} durationInFrames={10}>
    <PulseOpacity from={1.0} to={0.9} />
  </Sequence>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "lower_third_overlay",
  "position": { "x": 660, "y": 780 },
  "bars": [
    {
      "label": "Patches Applied",
      "color": "#F59E0B",
      "targetPercent": 105,
      "counterEnd": 2847,
      "suffix": " patches"
    },
    {
      "label": "Time Spent Repairing",
      "color": "#EF4444",
      "targetPercent": 102,
      "counterEnd": 1240,
      "suffix": " hrs"
    }
  ],
  "containerWidth": 600,
  "containerHeight": 160,
  "bgOpacity": 0.7
}
```
