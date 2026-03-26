[Remotion]

# Section 5.8: Economics Crossing Callback — The Threshold Pulses Again

**Tool:** Remotion
**Duration:** ~8s (240 frames @ 30fps)
**Timestamp:** 1:25 - 1:33

## Visual Description
A callback to the economics chart from Part 1 (the sock price chart with "The Threshold" crossing point). The chart fades in already fully drawn — the viewer recognizes it from earlier. But now the crossing point pulses with renewed emphasis: a bright golden glow that expands outward in concentric rings, like a radar ping. The message is clear: this is the moment the economics flipped. What was once rational (patching/darning) becomes irrational.

A new label appears below the crossing point: "The economics changed." This replaces the earlier "The Threshold" label, recontextualizing the same visual with the Part 5 argument.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Grid lines: inherited from Part 1 sock price chart style — horizontal dashed at `#1E293B` opacity `0.1`

### Chart/Visual Elements

#### Inherited Chart (from Section 1.2)
- X-axis: 1950 to 2020
- Y-axis: Cost (Labor Hours), 0 to 4
- Blue line ("Hour of labor"): `#4A90D9`, 3px, rising from ~1.0 to ~3.5
- Amber line ("Pair of wool socks"): `#D9944A`, 3px, falling from ~1.0 to ~0.08
- Both lines fully drawn (no animation — they appear complete)

#### Crossing Point (enhanced)
- Position: `(1962, 0.85)`
- Base dot: `10px`, `#FFFFFF`
- Glow ring 1: expands from `10px→40px` radius, `#D9944A` opacity `0.4→0`
- Glow ring 2: expands from `10px→70px` radius, `#D9944A` opacity `0.2→0` (delayed 15 frames)
- Glow ring 3: expands from `10px→100px` radius, `#D9944A` opacity `0.1→0` (delayed 30 frames)
- Rings repeat on a 90-frame cycle

#### New Label
- "The economics changed." — Inter, 18px, bold, `#E2E8F0`
- Position: centered below the crossing point, offset `+50px` below
- Appears with a subtle underline that draws left-to-right: `2px`, `#D9944A` opacity `0.5`

### Animation Sequence
1. **Frame 0-30 (0-1s):** The full chart fades in at once (opacity `0→1`). Both lines, axes, and labels are already complete. The viewer recognizes it immediately.
2. **Frame 30-60 (1-2s):** The crossing point begins pulsing. First glow ring expands outward.
3. **Frame 60-120 (2-4s):** All three rings pulsing in staggered sequence. The effect is like a beacon or radar ping emanating from the crossing.
4. **Frame 120-180 (4-6s):** "The economics changed." fades in below the crossing point. Underline draws left-to-right.
5. **Frame 180-240 (6-8s):** Hold. Crossing continues to pulse gently (single ring, quieter: opacity `0.15→0`).

### Typography
- New label: Inter, 18px, bold (700), `#E2E8F0`
- Inherited labels: Inter, 13px, respective line colors (from Part 1)
- Axis labels: Inter, 12px, `#475569` opacity `0.6`

### Easing
- Chart fade-in: `easeOutQuad` over 30 frames
- Ring expansion: `easeOutCubic` — fast start, slow dissipate
- Ring opacity fade: `linear` (simultaneous with expansion)
- Label fade-in: `easeOutQuad` over 25 frames
- Underline draw: `easeInOutCubic` over 30 frames

## Narration Sync
> "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={240}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Full chart fade-in (pre-drawn) */}
    <Sequence from={0}>
      <FadeIn durationInFrames={30}>
        <SockPriceChart
          xRange={[1950, 2020]} yRange={[0, 4]}
          laborData={[[1950, 1.0], [1960, 1.3], [1970, 1.8], [1980, 2.2], [1990, 2.6], [2000, 3.0], [2020, 3.5]]}
          garmentData={[[1950, 1.0], [1960, 0.7], [1965, 0.5], [1970, 0.35], [1980, 0.2], [2000, 0.12], [2020, 0.08]]}
          preDrawn={true} />
      </FadeIn>
    </Sequence>

    {/* Pulsing crossing point */}
    <Sequence from={30}>
      <GlowDot cx={1962} cy={0.85} radius={10} color="#FFFFFF" />
      <Loop durationInFrames={90}>
        <PulseRing cx={1962} cy={0.85}
          fromRadius={10} toRadius={40}
          color="#D9944A" fromOpacity={0.4} toOpacity={0}
          durationInFrames={45} easing="easeOutCubic" />
        <Sequence from={15}>
          <PulseRing cx={1962} cy={0.85}
            fromRadius={10} toRadius={70}
            color="#D9944A" fromOpacity={0.2} toOpacity={0}
            durationInFrames={50} easing="easeOutCubic" />
        </Sequence>
        <Sequence from={30}>
          <PulseRing cx={1962} cy={0.85}
            fromRadius={10} toRadius={100}
            color="#D9944A" fromOpacity={0.1} toOpacity={0}
            durationInFrames={55} easing="easeOutCubic" />
        </Sequence>
      </Loop>
    </Sequence>

    {/* New label */}
    <Sequence from={120}>
      <FadeIn durationInFrames={25}>
        <Text text="The economics changed." font="Inter"
          size={18} weight={700} color="#E2E8F0"
          x={1962} yOffset={50} align="center" />
        <AnimatedUnderline
          width={200} strokeWidth={2}
          color="#D9944A" opacity={0.5}
          drawDuration={30} easing="easeInOutCubic" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "callback_chart",
  "referencesSpec": "part1_economics/02_sock_price_chart",
  "crossingPoint": { "x": 1962, "y": 0.85 },
  "pulseEffect": {
    "rings": 3,
    "maxRadius": 100,
    "color": "#D9944A",
    "cycleDuration": 90
  },
  "newLabel": "The economics changed.",
  "narrationSegments": ["part5_compound_returns_009"]
}
```
