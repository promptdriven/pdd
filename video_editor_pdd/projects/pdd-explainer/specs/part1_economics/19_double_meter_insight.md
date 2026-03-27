[Remotion]

# Section 1.19: Double Meter Insight — Context Window + Model Performance

**Tool:** Remotion
**Duration:** ~12s (360 frames @ 30fps)
**Timestamp:** 8:04 - 8:16

## Visual Description

Two side-by-side vertical meters appear from the stillness, delivering the key synthesis. This is the payoff — the moment where two separate arguments combine into something greater than either.

**LEFT METER: "Effective Context Window"**
A vertical bar that animates from 1× at the bottom to 5-10× at the top. The bar fills with blue (`#4A90D9`), representing the compression advantage of working in prompt space. The label at the top reads "5-10×".

**RIGHT METER: "Model Performance"**
A vertical bar that animates upward, filling with green (`#5AAA6E`), representing the natural language advantage. The label at the top reads the peak performance level.

Both meters animate simultaneously — rising together. When both reach their peak, they pulse in unison. Text appears: "Bigger window AND smarter model."

The insight is: these aren't separate benefits — they compound. Working in prompt space gives you a bigger window AND better model performance at the same time.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (returns from the deeper black of the stillness)

### Chart/Visual Elements

#### Left Meter — Effective Context Window
- Position: x: 560, y: 200-800 (600px tall)
- Width: 80px
- Track: `#1E293B` fill, `#334155` 1px border, 8px corner radius
- Fill: `#4A90D9` at 0.7, fills from bottom to top
- Bottom label: "1×" — Inter 18px, `#64748B`
- Top label: "5-10×" — Inter 24px, bold (700), `#4A90D9`
- Title: "Effective Context Window" — Inter 16px, semi-bold (600), `#E2E8F0`, above meter

#### Right Meter — Model Performance
- Position: x: 1360, y: 200-800 (600px tall)
- Width: 80px
- Track: `#1E293B` fill, `#334155` 1px border, 8px corner radius
- Fill: `#5AAA6E` at 0.7, fills from bottom to top
- Bottom label: "Baseline" — Inter 14px, `#64748B`
- Top label: "+89%" — Inter 24px, bold (700), `#5AAA6E`
- Title: "Model Performance" — Inter 16px, semi-bold (600), `#E2E8F0`, above meter

#### Combined Text
- "Bigger window AND smarter model." — Inter 28px, bold (700), `#E2E8F0`
- Position: centered at y: 900
- "AND" in `#F59E0B` (accent highlight)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Background lightens from `#050810` to `#0A0F1A`. Meter tracks draw.
2. **Frame 30-60 (1-2s):** Meter titles appear. Bottom labels appear.
3. **Frame 60-180 (2-6s):** Both meters fill simultaneously. Blue rises on the left, green rises on the right. Smooth, satisfying animation.
4. **Frame 180-210 (6-7s):** Top labels appear. "5-10×" on left, "+89%" on right.
5. **Frame 210-270 (7-9s):** Both meters pulse together. Synchronized glow effect.
6. **Frame 270-330 (9-11s):** "Bigger window AND smarter model." text fades in.
7. **Frame 330-360 (11-12s):** Hold. Both meters at peak, text visible.

### Typography
- Meter titles: Inter, 16px, semi-bold (600), `#E2E8F0`
- Top values: Inter, 24px, bold (700), respective colors
- Bottom labels: Inter, 14-18px, regular (400), `#64748B`
- Insight text: Inter, 28px, bold (700), `#E2E8F0` with `#F59E0B` "AND"

### Easing
- Meter fill: `easeOut(cubic)` over 120 frames — smooth rise
- Pulse: `easeInOut(sine)` on 30-frame cycle, scale 1.0-1.02
- Text fade-in: `easeOut(quad)` over 30 frames
- Background lighten: `easeOut(quad)` over 30 frames

## Narration Sync
> "You saw that prompts are a fraction the size of the code they govern... your effective context window is 5 to 10 times larger, AND the model performs dramatically better."
> "A bigger window AND a smarter model. Not one or the other. Both. That's not an incremental improvement. That's a category shift."

Note: This narration actually belongs to Part 2's segments (the KEY INSIGHT subsection is at the end of Part 1 in the script). The visual here serves as the bridge.

- **~485.0s**: Meters begin rising
- **~490.0s**: Meters at peak, text appears

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={360}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Left meter: Context Window */}
    <VerticalMeter
      position={{ x: 560, y: 200 }}
      width={80} height={600}
      title="Effective Context Window"
      trackColor="#1E293B"
      fillColor="#4A90D9"
      bottomLabel="1×" topLabel="5-10×"
      fillStartFrame={60} fillDuration={120}
    />

    {/* Right meter: Model Performance */}
    <VerticalMeter
      position={{ x: 1360, y: 200 }}
      width={80} height={600}
      title="Model Performance"
      trackColor="#1E293B"
      fillColor="#5AAA6E"
      bottomLabel="Baseline" topLabel="+89%"
      fillStartFrame={60} fillDuration={120}
    />

    {/* Synchronized pulse */}
    <Sequence from={210}>
      <PulseScale targets={["left_meter", "right_meter"]}
        min={1.0} max={1.02}
        cycleFrames={30} synchronized />
    </Sequence>

    {/* Insight text */}
    <Sequence from={270}>
      <FadeIn duration={30}>
        <RichText
          parts={[
            { text: "Bigger window ", color: "#E2E8F0" },
            { text: "AND", color: "#F59E0B" },
            { text: " smarter model.", color: "#E2E8F0" }
          ]}
          font="Inter" size={28} weight={700}
          x={960} y={900} align="center"
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "double_meter",
  "chartId": "context_plus_performance",
  "meters": [
    {
      "id": "context_window",
      "title": "Effective Context Window",
      "fillColor": "#4A90D9",
      "bottomValue": "1×",
      "topValue": "5-10×",
      "position": "left"
    },
    {
      "id": "model_performance",
      "title": "Model Performance",
      "fillColor": "#5AAA6E",
      "bottomValue": "Baseline",
      "topValue": "+89%",
      "position": "right"
    }
  ],
  "insightText": "Bigger window AND smarter model.",
  "insightHighlight": { "word": "AND", "color": "#F59E0B" }
}
```

---
