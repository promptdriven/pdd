[Remotion] Dramatic Crossover Zoom — Generation Cost Below Both Lines

# Section 1.12: Crossover Zoom — The Economic Flip

**Tool:** Remotion
**Duration:** ~7s
**Timestamp:** 6:15 - 6:22

## Visual Description
A dramatic animated zoom into the crossover point from the cost chart (03_cost_crossover_chart.md). The entire chart rapidly zooms to 2.5x, centering on the intersection where "cost of generation" drops below "cost of patching." The crossover glow intensifies into a bright starburst. Text callouts appear: "Generation cost has crossed below both lines" and "80-90% of software cost is maintenance" — the thesis statement of Part 1. The starburst fades as the entire frame fades to black over the final 30 frames, ending Part 1.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay (composited over returning Veo cost graph footage)
- Zoom center: the crossover point from 03_cost_crossover_chart (approximately (770, 480) in chart coordinates)

### Chart/Visual Elements
- Inherited chart from 03_cost_crossover_chart, but zoomed 1.0→2.5x centered on crossover
- Crossover starburst: radial gradient burst, #F59E0B → #FFFFFF → transparent
  - Radius: 60px → 200px expansion
  - Opacity: 0.5 → 1.0 → 0.8 (bright flash then settle)
- Callout A: "Generation cost has crossed below both lines"
  - Position: above crossover point, offset up-right
  - Style: frosted glass pill, white text on dark backing
- Callout B: "80-90% of software cost is maintenance"
  - Position: below crossover point, offset down-left
  - Style: frosted glass pill, amber accent text
- Connecting lines: thin dotted lines from callouts to crossover point
- Fade to black: final 30 frames (frames 180-210), full-screen black overlay opacity 0→1

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Chart zooms — scale 1.0→2.5, transform-origin at crossover point. `easeInOutCubic`.
2. **Frame 20-50 (0.67-1.67s):** Starburst flash — radius 60→200px, opacity 0→1.0.
3. **Frame 40-60 (1.33-2s):** Starburst settles — opacity 1.0→0.8, holds with gentle pulse.
4. **Frame 50-80 (1.67-2.67s):** Callout A slides in from right — translateX(60)→0, opacity 0→1.
5. **Frame 70-100 (2.33-3.33s):** Callout B slides in from left — translateX(-60)→0, opacity 0→1.
6. **Frame 80-100 (2.67-3.33s):** Connecting dotted lines draw from callouts to crossover.
7. **Frame 100-180 (3.33-6s):** Hold. Starburst gently pulses.
8. **Frame 180-210 (6-7s):** Fade to black — full-screen black overlay, opacity 0→1.

### Typography
- Callout A: Inter Bold, 28px, #FFFFFF
  - Background: rgba(15, 23, 42, 0.85), backdrop-filter blur(8px), border-radius 12px, padding 16px 24px
- Callout B: Inter Bold, 26px, #F59E0B
  - Background: rgba(15, 23, 42, 0.85), backdrop-filter blur(8px), border-radius 12px, padding 16px 24px
- Connecting lines: dotted, 1.5px, #94A3B8 at 50% opacity

### Easing
- Chart zoom: `easeInOutCubic`
- Starburst flash: `easeOutQuart`
- Starburst pulse (hold): sinusoidal, 1.5s period, opacity [0.7, 0.9]
- Callout slides: `spring({ damping: 14, stiffness: 160 })`
- Fade to black: `easeInQuad`

## Narration Sync
> "Generation cost has crossed below both lines. Debt resets. 80 to 90 percent of software cost is maintenance — and that line just moved."

The zoom triggers as "Generation cost has crossed" begins. "80 to 90 percent" callout appears in sync. Fade to black on "and that line just moved."

## Code Structure (Remotion)
```typescript
<Sequence from={CROSSOVER_ZOOM_START} durationInFrames={210}>
  <AbsoluteFill>
    {/* Zooming chart */}
    <div style={{
      transform: `scale(${interpolate(frame, [0, 40], [1.0, 2.5], {
        easing: Easing.inOut(Easing.cubic),
        extrapolateRight: 'clamp',
      })})`,
      transformOrigin: '770px 480px',
    }}>
      <CostCrossoverChart frame={chartEndFrame} /> {/* Static at final state */}
    </div>

    {/* Starburst at crossover */}
    <Starburst
      center={[770, 480]}
      radius={interpolate(frame, [20, 50], [60, 200], { extrapolateRight: 'clamp' })}
      opacity={interpolate(frame, [20, 35, 50, 180, 210], [0, 1.0, 0.8, 0.8, 0])}
      pulseOpacity={frame > 50 ? interpolate(Math.sin(frame * 0.14), [-1, 1], [0.7, 0.9]) : undefined}
      color="#F59E0B"
    />

    {/* Callout A */}
    <Sequence from={50} durationInFrames={160}>
      <CalloutPill
        text="Generation cost has crossed below both lines"
        position="top-right"
        style={{
          transform: `translateX(${interpolate(frame, [0, 30], [60, 0])}px)`,
          opacity: interpolate(frame, [0, 30, 130, 160], [0, 1, 1, 0]),
        }}
      />
    </Sequence>

    {/* Callout B */}
    <Sequence from={70} durationInFrames={140}>
      <CalloutPill
        text="80-90% of software cost is maintenance"
        position="bottom-left"
        color="#F59E0B"
        style={{
          transform: `translateX(${interpolate(frame, [0, 30], [-60, 0])}px)`,
          opacity: interpolate(frame, [0, 30, 110, 140], [0, 1, 1, 0]),
        }}
      />
    </Sequence>

    {/* Fade to black */}
    <AbsoluteFill style={{
      backgroundColor: '#000000',
      opacity: interpolate(frame, [180, 210], [0, 1], { extrapolateLeft: 'clamp' }),
    }} />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "zoom_target": {"x": 770, "y": 480},
  "zoom_scale": 2.5,
  "callouts": [
    {"text": "Generation cost has crossed below both lines", "color": "#FFFFFF"},
    {"text": "80-90% of software cost is maintenance", "color": "#F59E0B"}
  ],
  "starburst_color": "#F59E0B",
  "fade_to_black_start_frame": 180,
  "totalFrames": 210,
  "fps": 30
}
```

---
