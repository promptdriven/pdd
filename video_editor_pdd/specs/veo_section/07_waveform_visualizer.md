[Remotion]

# Section 2.7: Narration Waveform Visualizer

**Tool:** Remotion
**Duration:** ~3s
**Timestamp:** 0:08 - 0:11

## Visual Description
A minimal audio waveform visualization that floats above the split-screen summary, reinforcing the "narration overlay" concept. A horizontal band of vertical bars oscillates to represent the narration audio amplitude. The bars pulse in warm gold tones against a translucent dark backdrop, creating a visual echo of the spoken words. A small label reads "NARRATION SYNC" to the left, and a playhead indicator sweeps from left to right across the waveform.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent (overlaid on split-screen or dark background)
- Grid lines: none

### Chart/Visual Elements
- Waveform container: centered at (960, 280), 800px wide, 120px tall
- Backdrop panel: 860x150px, background rgba(15, 20, 25, 0.75), borderRadius 12px, border 1px rgba(212, 165, 116, 0.2)
- Waveform bars: 64 vertical bars, each 6px wide, spacing 6.5px, centered vertically within container
  - Bar heights: oscillate between 8px and 100px based on amplitude data
  - Bar color: warm gold gradient (#D4A574 base → #F59E0B peaks)
  - Bar borderRadius: 3px
- Playhead: 2px wide, full container height, color #F8FAFC at 80% opacity, moves left→right
- Label "NARRATION SYNC": positioned at (600, 230), uppercase
- Timestamp counter: positioned at (1320, 230), displays elapsed time "0:08 / 0:11"

### Animation Sequence
1. **Frame 0-12 (0-0.4s):** Backdrop panel fades in (opacity 0→1). Label and timestamp fade in.
2. **Frame 8-20 (0.27-0.67s):** Waveform bars grow from center (scaleY 0→1), staggered left-to-right (2 frame delay per bar group of 8).
3. **Frame 20-75 (0.67-2.5s):** Bars oscillate based on amplitude keyframes. Playhead sweeps left→right. Timestamp counter increments.
4. **Frame 75-90 (2.5-3.0s):** All elements fade out (opacity 1→0). Bars shrink to center.

### Typography
- Label: Inter SemiBold, 13px, warm gold (#D4A574), tracking 2.5px, uppercase
- Timestamp: JetBrains Mono, 13px, slate (#94A3B8)

### Easing
- Backdrop fade: `easeOutQuad`
- Bar stagger grow: `easeOutBack` (slight overshoot)
- Bar oscillation: `easeInOutSine` (smooth wave)
- Playhead sweep: `linear`
- Fade out: `easeInCubic`

## Narration Sync
> (No narration — visual beat bridging narration section to summary)

## Code Structure (Remotion)
```typescript
<Sequence from={240} durationInFrames={90}>
  <AbsoluteFill>
    <FadeIn duration={12}>
      <BackdropPanel width={860} height={150} blur={0} opacity={0.75} borderRadius={12}>
        <Label text="NARRATION SYNC" color="#D4A574" position={[600, 230]} />
        <TimestampCounter start="0:08" end="0:11" position={[1320, 230]} />
        <Sequence from={8}>
          <WaveformBars
            barCount={64}
            barWidth={6}
            maxHeight={100}
            colors={["#D4A574", "#F59E0B"]}
            amplitudeData={amplitudeKeyframes}
            staggerDelay={2}
          />
        </Sequence>
        <Sequence from={20}>
          <Playhead color="#F8FAFACC" duration={55} />
        </Sequence>
      </BackdropPanel>
    </FadeIn>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "barCount": 64,
  "barWidth": 6,
  "maxBarHeight": 100,
  "waveformColors": ["#D4A574", "#F59E0B"],
  "containerWidth": 800,
  "containerHeight": 120,
  "amplitudeKeyframes": [
    0.2, 0.4, 0.7, 0.9, 0.6, 0.3, 0.5, 0.8,
    0.95, 0.7, 0.4, 0.2, 0.6, 0.85, 0.5, 0.3
  ],
  "playheadDuration": 55
}
```

---
