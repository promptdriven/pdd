[Remotion]

# Section 1.15: Double Meter Insight — Context Window + Model Performance

**Tool:** Remotion
**Duration:** ~14s (420 frames @ 30fps)
**Timestamp:** 7:21 - 7:35

## Visual Description

Two side-by-side vertical meters that deliver the synthesis of the entire economics argument. This is the "one more thing" payoff.

**LEFT meter — "Effective Context Window":** A vertical bar that starts at 1× and animates upward to 5-10×. The bar fills with a gradient from `#4A90D9` (cool blue) at the bottom to `#2DD4BF` (teal) at the top. Scale markers on the side: 1×, 2×, 5×, 10×.

**RIGHT meter — "Model Performance":** A vertical bar that rises steadily. Filled with `#22C55E` (green). It represents the fact that models are getting smarter AND the context they're working with is cleaner.

Both meters animate simultaneously — this is the double benefit. When patching, you only get one improvement (smarter model). With PDD regeneration, you get BOTH (smarter model AND effectively larger context window because the context is curated, not stuffed with code).

At peak, both meters pulse together. Text appears: "Bigger window AND smarter model."

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid lines — clean, focused

### Chart/Visual Elements

#### Left Meter — Effective Context Window
- Position: centered at x: 600
- Frame: rounded rect, 120×600px, `#1E293B` fill, `#334155` border at 0.3, rounded 8px
- Fill bar: gradient `#4A90D9` → `#2DD4BF`, animates from 0% to 85% height
- Scale markers: "1×" at bottom, "2×", "5×", "10×" at top — Inter, 12px, `#94A3B8` at 0.5
- Label below: "Effective Context Window" — Inter, 16px, bold, `#4A90D9`
- Glow at top of filled bar: `#2DD4BF` at 0.15, 12px radius

#### Right Meter — Model Performance
- Position: centered at x: 1360
- Frame: rounded rect, 120×600px, `#1E293B` fill, `#334155` border at 0.3, rounded 8px
- Fill bar: solid `#22C55E`, animates from 20% to 80% height
- Scale markers: subtle horizontal lines every 20% — `#334155` at 0.1
- Label below: "Model Performance" — Inter, 16px, bold, `#22C55E`
- Glow at top of filled bar: `#22C55E` at 0.15, 12px radius

#### Center Annotation
- "×" symbol between the meters: Inter, 48px, bold, `#E2E8F0` at 0.3, centered at (960, 540)
- After both peak: "Bigger window AND smarter model." — Inter, 18px, bold, `#E2E8F0`, centered at (960, 820)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Meter frames appear. Labels fade in below each.
2. **Frame 30-60 (1-2s):** Scale markers appear on left meter.
3. **Frame 60-210 (2-7s):** Both meters begin filling simultaneously. Left meter rises from 1× toward 10×. Right meter rises steadily.
4. **Frame 210-270 (7-9s):** Both meters reach peak. Glow appears at top of each. "×" symbol pulses between them.
5. **Frame 270-330 (9-11s):** "Bigger window AND smarter model." text appears.
6. **Frame 330-420 (11-14s):** Hold. Both meters pulse together in sync. The synthesis lands.

### Typography
- Meter labels: Inter, 16px, bold (700), respective colors
- Scale markers: Inter, 12px, `#94A3B8` at 0.5
- "×" symbol: Inter, 48px, bold (700), `#E2E8F0` at 0.3
- Summary text: Inter, 18px, bold (700), `#E2E8F0`

### Easing
- Meter frame appear: `easeOut(quad)` over 20 frames
- Bar fill: `easeInOut(cubic)` over 150 frames — smooth, satisfying rise
- Glow at peak: `easeOut(back)` over 15 frames — slight overshoot bloom
- Summary text: `easeOut(quad)` over 25 frames
- Pulse: `easeInOut(sine)` on 45-frame cycle — both meters in sync

## Narration Sync
> "Tools like Cursor and Claude Code are incredible for patching."
> "But they're still darning needles. Faster needles. AI-powered needles. But needles."

Segments: `part1_economics_032`, `part1_economics_033`

- **441.12s** ("Tools like Cursor"): Meters appear, begin filling
- **448.18s** ("But they're still darning needles"): Meters at peak, summary text appears
- **455.44s** (end): Hold at peak

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={420}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left meter — Effective Context Window */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <MeterFrame x={600} y={240} width={120} height={600}
          bg="#1E293B" border="#334155" borderOpacity={0.3} />
        <Text text="Effective Context Window" font="Inter" size={16}
          weight={700} color="#4A90D9" x={600} y={880} align="center" />
      </FadeIn>
    </Sequence>

    {/* Left meter fill */}
    <Sequence from={60}>
      <MeterFill
        x={600} y={240} width={120} height={600}
        fillPercent={85} fillDuration={150}
        gradient={{ from: "#4A90D9", to: "#2DD4BF" }}
        glow={{ color: "#2DD4BF", opacity: 0.15, radius: 12 }}
        scaleMarkers={["1×", "2×", "5×", "10×"]} />
    </Sequence>

    {/* Right meter — Model Performance */}
    <Sequence from={0}>
      <FadeIn duration={20}>
        <MeterFrame x={1360} y={240} width={120} height={600}
          bg="#1E293B" border="#334155" borderOpacity={0.3} />
        <Text text="Model Performance" font="Inter" size={16}
          weight={700} color="#22C55E" x={1360} y={880} align="center" />
      </FadeIn>
    </Sequence>

    {/* Right meter fill */}
    <Sequence from={60}>
      <MeterFill
        x={1360} y={240} width={120} height={600}
        fillPercent={80} fillDuration={150}
        color="#22C55E"
        glow={{ color: "#22C55E", opacity: 0.15, radius: 12 }} />
    </Sequence>

    {/* Center × symbol */}
    <Sequence from={210}>
      <PulsingText text="×" font="Inter" size={48}
        weight={700} color="#E2E8F0" opacity={0.3}
        x={960} y={540} cycleFrames={45} />
    </Sequence>

    {/* Summary text */}
    <Sequence from={270}>
      <FadeIn duration={25}>
        <Text text="Bigger window AND smarter model."
          font="Inter" size={18} weight={700} color="#E2E8F0"
          x={960} y={820} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "dual_meter_visualization",
  "meters": [
    {
      "id": "effective_context_window",
      "label": "Effective Context Window",
      "color": { "from": "#4A90D9", "to": "#2DD4BF" },
      "scaleMarkers": ["1×", "2×", "5×", "10×"],
      "fillPercent": 85,
      "position": "left"
    },
    {
      "id": "model_performance",
      "label": "Model Performance",
      "color": "#22C55E",
      "fillPercent": 80,
      "position": "right"
    }
  ],
  "summary": "Bigger window AND smarter model.",
  "narrationSegments": ["part1_economics_032", "part1_economics_033"]
}
```

---
