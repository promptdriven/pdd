[Remotion]

# Section 2.3: Wave Data Overlay

**Tool:** Remotion
**Duration:** ~2s
**Timestamp:** 0:10 – 0:12

## Visual Description
A data visualization overlay composited on top of the ocean wave footage. A sinusoidal waveform graph animates across the lower third of the screen, representing ocean wave patterns. Three stat callout badges appear in sequence showing wave height, wave period, and water temperature. A subtle gradient overlay at the bottom provides contrast for the data elements against the video.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: Transparent overlay on top of veo clip
- Gradient overlay at bottom: `linear-gradient(transparent, rgba(11,17,32,0.85))` occupying lower 40% of frame

### Chart/Visual Elements
- **Waveform Graph:** Sine wave path, amplitude 0.8, frequency 1.2, 120 data samples
  - Stroke: `#C9A84C` (gold), 2px
  - Fill below curve: `rgba(201,168,76,0.15)`
  - Position: lower third, y-center at 780px
- **Grid Overlay:** Subtle dashed lines, `rgba(255,255,255,0.08)`, 4 horizontal + 6 vertical
- **Stat Badge 1 — Wave Height:** "0.8m" with wave icon, positioned top-left of data area (x:120, y:680)
- **Stat Badge 2 — Wave Period:** "6.2s" with clock icon, positioned center (x:860, y:680)
- **Stat Badge 3 — Water Temp:** "22°C" with thermometer icon, positioned top-right (x:1600, y:680)
- **Accent Dots:** Small gold dots (`#C9A84C`) at waveform peaks, 4px radius

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Gradient overlay fades in. Grid lines draw on with horizontal-first then vertical.
2. **Frame 10–40 (0.33–1.33s):** Waveform path draws from left to right using `strokeDashoffset` animation. Accent dots appear as the wave passes each peak.
3. **Frame 20–30 (0.67–1.0s):** Stat Badge 1 (Wave Height) slides up and fades in.
4. **Frame 30–40 (1.0–1.33s):** Stat Badge 2 (Wave Period) slides up and fades in.
5. **Frame 40–50 (1.33–1.67s):** Stat Badge 3 (Water Temp) slides up and fades in.
6. **Frame 50–60 (1.67–2.0s):** All elements hold. Subtle pulse animation on waveform amplitude.

### Typography
- Stat values: Inter Bold, 32px, `#FFFFFF`
- Stat labels: Inter Regular, 14px, `rgba(255,255,255,0.7)`
- Units: Inter Medium, 20px, `#C9A84C`

### Easing
- Waveform draw: `linear` (constant speed trace)
- Stat badge slide-up: `easeOutBack` (slight overshoot)
- Grid fade: `easeOutQuad`
- Gradient overlay: `easeInQuad`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <GradientOverlay />
  <GridOverlay />
  <Sequence from={10}>
    <SineWavePath
      amplitude={0.8}
      frequency={1.2}
      samples={120}
    />
    <AccentDots />
  </Sequence>
  <Sequence from={20}>
    <StatBadge label="Wave Height" value="0.8m" />
  </Sequence>
  <Sequence from={30}>
    <StatBadge label="Wave Period" value="6.2s" />
  </Sequence>
  <Sequence from={40}>
    <StatBadge label="Water Temp" value="22°C" />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "waveform": {
    "amplitude": 0.8,
    "frequency": 1.2,
    "samples": 120
  },
  "stats": [
    { "label": "Wave Height", "value": "0.8m", "icon": "wave" },
    { "label": "Wave Period", "value": "6.2s", "icon": "clock" },
    { "label": "Water Temp", "value": "22°C", "icon": "thermometer" }
  ]
}
```

---
