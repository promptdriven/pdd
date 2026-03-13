[Remotion]

# Section 2.4: Wave Data Overlay

**Tool:** Remotion
**Duration:** ~1.3s
**Timestamp:** 0:04 - 0:05

## Visual Description
An animated data visualization overlaid on a still frame extracted from the ocean Veo footage. A sinusoidal wave-amplitude graph draws itself across the screen from left to right, representing ocean wave height data. The chart appears over a darkened/blurred version of the ocean clip. Key metrics animate in as floating stat callouts: "Wave Height: 1.2m", "Period: 8.4s", "Water Temp: 22C". This demonstrates the pipeline's ability to composite Remotion data graphics on top of Veo-sourced imagery.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Blurred still from ocean footage with dark overlay rgba(10, 22, 40, 0.7)
- Grid lines: Subtle horizontal grid at y=300, 400, 500, 600 — color rgba(255,255,255,0.08)

### Chart/Visual Elements
- **Wave amplitude chart:**
  - X-axis: Time (0-10s), positioned at y=700, labels every 2s
  - Y-axis: Amplitude (-1.5m to +1.5m), positioned at x=160, labels every 0.5m
  - Line: Sinusoidal curve, stroke #4DA8DA, strokeWidth 3, with glow effect (drop-shadow 0 0 8px #4DA8DA)
  - Fill: Gradient from #4DA8DA (opacity 0.3) to transparent below the curve
- **Stat callouts (3 floating badges):**
  - Badge 1: "Wave Height: 1.2m" at position (1400, 200), bg rgba(77,168,218,0.2), border #4DA8DA
  - Badge 2: "Period: 8.4s" at position (1500, 320), bg rgba(77,168,218,0.2), border #4DA8DA
  - Badge 3: "Water Temp: 22C" at position (1450, 440), bg rgba(77,168,218,0.2), border #4DA8DA
- **Chart title:** "WAVE ANALYSIS" at top-left (80, 80)

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Background still fades in. Grid lines draw from left to right. Axes appear.
2. **Frame 8-28 (0.27-0.93s):** Sinusoidal wave line draws progressively from left to right using `strokeDashoffset` animation. Fill gradient follows behind the line.
3. **Frame 20-34 (0.67-1.13s):** Stat callout badges pop in sequentially (staggered by 4 frames each), scaling from 0.8 → 1.0 with fade.
4. **Frame 34-38 (1.13-1.27s):** All elements hold steady.

### Typography
- Chart title: Inter Bold, 28px, #FFFFFF, letter-spacing 6px, opacity 0.9
- Axis labels: Inter Regular, 14px, rgba(255,255,255,0.5)
- Stat badge values: Inter SemiBold, 18px, #FFFFFF
- Stat badge labels: Inter Regular, 14px, #8EC8E8

### Easing
- Wave line draw: `linear` (constant speed reveal)
- Stat badge pop-in: `easeOutBack` (slight overshoot)
- Grid line draw: `easeOutQuad`

## Narration Sync
> "This is the second section of the integration test video."
(Narration from previous beat may still be audible during this overlay)

## Code Structure (Remotion)
```typescript
<Sequence from={114} durationInFrames={38}>
  <AbsoluteFill>
    <BlurredStillBackground src={staticFile("veo/04_veo_broll.mp4")} frame={15} />
    <DarkOverlay opacity={0.7} />
    <GridLines rows={4} color="rgba(255,255,255,0.08)" />
    <Sequence from={0}>
      <ChartAxes xLabel="Time (s)" yLabel="Amplitude (m)" />
    </Sequence>
    <Sequence from={8}>
      <SineWaveLine
        amplitude={1.2}
        frequency={0.75}
        color="#4DA8DA"
        strokeWidth={3}
      />
    </Sequence>
    <Sequence from={20}>
      <StatCallout label="Wave Height" value="1.2m" position={{ x: 1400, y: 200 }} delay={0} />
      <StatCallout label="Period" value="8.4s" position={{ x: 1500, y: 320 }} delay={4} />
      <StatCallout label="Water Temp" value="22°C" position={{ x: 1450, y: 440 }} delay={8} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "chartTitle": "WAVE ANALYSIS",
  "waveData": {
    "amplitude": 1.2,
    "period": 8.4,
    "waterTemp": 22,
    "unit": "meters"
  },
  "series": [
    { "time": 0, "height": 0.0 },
    { "time": 1, "height": 0.9 },
    { "time": 2, "height": 1.2 },
    { "time": 3, "height": 0.8 },
    { "time": 4, "height": -0.3 },
    { "time": 5, "height": -1.0 },
    { "time": 6, "height": -1.2 },
    { "time": 7, "height": -0.6 },
    { "time": 8, "height": 0.4 },
    { "time": 9, "height": 1.1 },
    { "time": 10, "height": 1.2 }
  ]
}
```
