[Remotion]

# Section 2.4: Wave Data Overlay

**Tool:** Remotion
**Duration:** ~1.0s
**Timestamp:** 0:12 – 0:13

## Visual Description
A data visualization overlay composited on top of a still frame (or looping segment) from the ocean wave footage. A sinusoidal waveform graph animates from left to right across the lower third of the screen, representing the rhythm of the ocean wave. Key metrics — wave height, period, and water temperature — appear as floating stat badges in the upper-right quadrant. The effect blends cinematic footage with a clean infographic aesthetic.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Semi-transparent dark overlay (#0B1120 at 60% opacity) over Veo footage still
- Grid lines: Subtle horizontal grid at 25% intervals, color #FFFFFF at 5% opacity

### Chart/Visual Elements
- **Waveform graph (lower third):**
  - Area: x: 100–1820, y: 680–980
  - Sine wave path: stroke #4FC3F7 (light blue), 3px, with soft glow (#4FC3F7 at 30% opacity, blur 8px)
  - Fill beneath curve: linear gradient from #4FC3F7 at 20% opacity → transparent
  - X-axis: implicit (time), no labels
  - Y-axis: implicit (amplitude), no labels
- **Stat badges (upper-right, y: 80–300, x: 1400–1840):**
  - Badge 1: "Wave Height" — value "0.8m" — icon: wave glyph
  - Badge 2: "Period" — value "6.2s" — icon: clock glyph
  - Badge 3: "Temperature" — value "22°C" — icon: thermometer glyph
  - Each badge: 380x60px rounded rect (radius 12px), fill #1A2744 at 80% opacity, border 1px #4FC3F7 at 40%

### Animation Sequence
1. **Frame 0–8 (0–0.27s):** Dark overlay fades in (opacity 0→60%). Grid lines fade in simultaneously
2. **Frame 8–22 (0.27–0.73s):** Waveform draws left-to-right using `strokeDashoffset` animation. Glow activates as the line draws
3. **Frame 8–12 (0.27–0.4s):** Badge 1 slides in from right (translateX +40→0, opacity 0→1)
4. **Frame 12–16 (0.4–0.53s):** Badge 2 slides in (staggered)
5. **Frame 16–20 (0.53–0.67s):** Badge 3 slides in (staggered)
6. **Frame 22–30 (0.73–1.0s):** Hold — all elements fully visible

### Typography
- Badge label: Inter Medium, 14px, muted silver (#A0AEC0)
- Badge value: Inter Bold, 22px, white (#FFFFFF)
- No axis labels

### Easing
- Overlay fade: `easeOutQuad`
- Waveform draw: `linear` (constant draw speed)
- Badge slide-in: `easeOutCubic`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={30}>
  <AbsoluteFill style={{ backgroundColor: "rgba(11,17,32,0.6)" }}>
    <WaveformGraph
      amplitude={0.8}
      frequency={1.2}
      strokeColor="#4FC3F7"
      drawDurationFrames={14}
    />
    <Sequence from={8}>
      <StatBadge label="Wave Height" value="0.8m" delay={0} />
    </Sequence>
    <Sequence from={12}>
      <StatBadge label="Period" value="6.2s" delay={0} />
    </Sequence>
    <Sequence from={16}>
      <StatBadge label="Temperature" value="22°C" delay={0} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "wave_height_m": 0.8,
  "wave_period_s": 6.2,
  "water_temp_c": 22,
  "waveform": {
    "amplitude": 0.8,
    "frequency": 1.2,
    "samples": 120
  }
}
```

---
