[Remotion]

# Section 2.9: Waveform Visualizer

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:24 - 0:27

## Visual Description
An audio waveform visualizer animates across the bottom of the screen, representing the narration audio track. The waveform is rendered as a series of vertical bars that bounce reactively, styled in a gradient from amber to emerald. A thin timeline scrubber line moves left-to-right across the waveform, and a small timestamp counter ticks in the corner. This visual reinforces the audio/narration integration aspect of the Veo pipeline.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark charcoal (#121212) with subtle noise grain at 2% opacity

### Chart/Visual Elements
- Waveform bars: 64 vertical bars, each 8px wide with 4px gap, centered horizontally at Y baseline=900
  - Height range: 20px to 200px, animated pseudo-randomly per bar
  - Color gradient: Left bars #F59E0B (amber), center blend, right bars #34D399 (emerald)
  - Bar corners: borderRadius 4px top
- Timeline scrubber: Vertical line, 2px, #FFFFFF at 60% opacity, moves left-to-right across waveform area
- Timestamp counter: "0:24" incrementing to "0:27", top-right corner (X=1800, Y=40)
- Section label: "NARRATION AUDIO" small text above waveform, centered

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Waveform bars grow from 0px to their initial heights, staggered left-to-right with 1-frame delay per bar. Section label fades in.
2. **Frame 15-75 (0.5-2.5s):** Bars animate continuously — each bar oscillates between 40% and 100% of its max height in a wave pattern (sine wave offset by bar index). Scrubber line moves from left edge to right edge of waveform. Timestamp counter ticks.
3. **Frame 75-90 (2.5-3s):** Bars shrink back to 0px height, staggered right-to-left. Label and timestamp fade out.

### Typography
- Section label: Inter Medium, 14px, #FFFFFF at 50% opacity, letter-spacing 3px, uppercase
- Timestamp: JetBrains Mono, 18px, #FFFFFF at 70% opacity

### Easing
- Bar grow/shrink: `easeOutQuad`
- Bar oscillation: `sinusoidal` (Math.sin based)
- Scrubber: `linear`
- Fade in/out: `easeInOutQuad`

## Narration Sync
> (No narration — ambient audio visualization beat)

## Code Structure (Remotion)
```typescript
<Sequence from={720} durationInFrames={90}>
  <WaveformBackground grain={0.02} />
  <SectionLabel text="NARRATION AUDIO" y={680} />
  <WaveformBars
    barCount={64}
    barWidth={8}
    gap={4}
    baselineY={900}
    maxHeight={200}
    gradientStart="#F59E0B"
    gradientEnd="#34D399"
  />
  <TimelineScrubber color="rgba(255, 255, 255, 0.6)" />
  <TimestampCounter start="0:24" end="0:27" position={{ x: 1800, y: 40 }} />
</Sequence>
```

## Data Points
```json
{
  "barCount": 64,
  "barWidth": 8,
  "maxHeight": 200,
  "gradientStart": "#F59E0B",
  "gradientEnd": "#34D399",
  "timeRange": ["0:24", "0:27"]
}
```

---
