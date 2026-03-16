[Remotion]

# Section 2.2: Category Shift — Double Meter

**Tool:** Remotion
**Duration:** ~18s (540 frames @ 30fps)
**Timestamp:** 8:34 - 8:52

## Visual Description
Two vertical meter gauges side by side visualize the compounding advantage of working in prompt space. The LEFT meter is labeled "Effective Context Window" and fills upward from 1x to 5-10x, colored in a teal gradient. The RIGHT meter is labeled "Model Performance" and fills upward from a baseline to a high mark, colored in warm amber. Both meters animate upward sequentially, then a glowing connector bar links them at the top with the label "Both. At once." — emphasizing this is not one-or-the-other but a multiplicative gain. A callout card below challenges the viewer: "Try it yourself." The background is dark navy with faint radial glow behind the meters.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Dark navy `#0F172A` with subtle radial gradient `rgba(74,144,217,0.05)` centered at (960, 400), radius 500px
- Grid lines: None

### Chart/Visual Elements
- **Left Meter — Context Window**
  - Position: X=360, Y=180 (top of meter track)
  - Track: 80px wide x 500px tall, rounded corners 8px, fill `rgba(255,255,255,0.06)`, 1px border `rgba(255,255,255,0.1)`
  - Fill bar: 72px wide, grows from bottom, gradient `#2AA198` (bottom) to `#5EEAD4` (top)
  - Label above: "Effective Context Window" — `#94A3B8`, 20px
  - Value label (inside fill, near top): "5–10×" — `#FFFFFF`, 28px, bold
  - Baseline mark: Thin line at 10% height, label "1×" — `rgba(255,255,255,0.4)`
- **Right Meter — Model Performance**
  - Position: X=1480, Y=180 (top of meter track)
  - Track: 80px wide x 500px tall, same style as left
  - Fill bar: 72px wide, grows from bottom, gradient `#D9944A` (bottom) to `#FBBF24` (top)
  - Label above: "Model Performance" — `#94A3B8`, 20px
  - Value label (inside fill, near top): "Dramatically Better" — `#FFFFFF`, 20px, bold
  - Baseline mark: Thin line at 30% height, label "Code Input" — `rgba(255,255,255,0.4)`
- **Connector Bar**
  - Horizontal glowing line from top of left fill to top of right fill, Y≈230px
  - Color: `#FFFFFF` at 0.6 opacity, 2px, with `rgba(255,255,255,0.2)` blur 8px glow
  - Center label: "Both. At once." — `#FFFFFF`, 26px, bold
- **Callout Card**
  - Positioned below meters, centered at Y=780px
  - Rounded rectangle 600px x 80px, border `rgba(255,255,255,0.15)`, fill `rgba(255,255,255,0.03)`
  - Text: "Try it yourself. Give an LLM the same problem as code, then as natural language." — `#CBD5E1`, 18px

### Animation Sequence
1. **Frame 0-30 (0-1s):** Meter tracks and labels fade in. Baseline marks appear
2. **Frame 30-120 (1-4s):** Left meter fill rises from baseline to 90% height (5-10× mark). Value label "5–10×" fades in as fill reaches top
3. **Frame 90-180 (3-6s):** Right meter fill rises from baseline to 85% height. Value label "Dramatically Better" fades in
4. **Frame 180-240 (6-8s):** Connector bar draws from left to right. Center label "Both. At once." scales in from 0.8→1.0 with glow pulse
5. **Frame 240-300 (8-10s):** Hold on the connected meters. Subtle ambient glow pulse on connector (opacity oscillates 0.5-0.7)
6. **Frame 300-360 (10-12s):** All meter elements dim to 60% opacity. Callout card slides up from Y=840→780 and fades in
7. **Frame 360-450 (12-15s):** Hold on callout card
8. **Frame 450-540 (15-18s):** Everything fades out to 0 opacity over 90 frames

### Typography
- Meter Labels: Inter, 20px, semi-bold (600), `#94A3B8`
- Value Labels: Inter, 28px, bold (700), `#FFFFFF`
- Connector Label: Inter, 26px, bold (700), `#FFFFFF`
- Callout Text: Inter, 18px, regular (400), `#CBD5E1`

### Easing
- Meter fill rise: `easeOut(cubic)`
- Value label fade: `easeOut(quad)`
- Connector draw: `easeInOut(cubic)`
- Connector label scale: `easeOut(back(1.3))`
- Glow pulse: `easeInOut(sine)` (looping)
- Callout slide: `easeOut(cubic)`
- Final fade-out: `easeIn(quad)`

## Narration Sync
> "You saw that prompts are a fraction the size of the code they govern. And you saw that natural language is what these models do best. That means working in prompt space gives you two things at once: your effective context window is five to ten times larger, AND the model performs dramatically better on every token in it."
> "A bigger window AND a smarter model. Not one or the other. Both. That's not an incremental improvement. That's a category shift."
> "Try it yourself. Take your favorite LLM, give it a hard coding problem as code, then give it the same problem described in natural language. The natural language version will win."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={540}>
  {/* Meter Tracks */}
  <Sequence from={0} durationInFrames={30}>
    <MeterTrack x={360} y={180} width={80} height={500} label="Effective Context Window" />
    <MeterTrack x={1480} y={180} width={80} height={500} label="Model Performance" />
  </Sequence>

  {/* Left Meter Fill */}
  <Sequence from={30} durationInFrames={90}>
    <MeterFill
      x={360} y={180} width={72} maxHeight={450}
      gradientFrom="#2AA198" gradientTo="#5EEAD4"
      valueLabel="5–10×"
    />
  </Sequence>

  {/* Right Meter Fill */}
  <Sequence from={90} durationInFrames={90}>
    <MeterFill
      x={1480} y={180} width={72} maxHeight={425}
      gradientFrom="#D9944A" gradientTo="#FBBF24"
      valueLabel="Dramatically Better"
    />
  </Sequence>

  {/* Connector Bar */}
  <Sequence from={180} durationInFrames={60}>
    <ConnectorBar
      fromX={440} toX={1480} y={230}
      label="Both. At once."
      glowColor="rgba(255,255,255,0.2)"
    />
  </Sequence>

  {/* Callout Card */}
  <Sequence from={300} durationInFrames={60}>
    <CalloutCard
      y={780} width={600} height={80}
      text="Try it yourself. Give an LLM the same problem as code, then as natural language."
    />
  </Sequence>

  {/* Fade Out */}
  <Sequence from={450} durationInFrames={90}>
    <FadeOut />
  </Sequence>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "meters": {
    "left": {
      "x": 360,
      "label": "Effective Context Window",
      "trackHeight": 500,
      "fillPercent": 0.9,
      "gradientFrom": "#2AA198",
      "gradientTo": "#5EEAD4",
      "valueLabel": "5–10×",
      "baselinePercent": 0.1,
      "baselineLabel": "1×"
    },
    "right": {
      "x": 1480,
      "label": "Model Performance",
      "trackHeight": 500,
      "fillPercent": 0.85,
      "gradientFrom": "#D9944A",
      "gradientTo": "#FBBF24",
      "valueLabel": "Dramatically Better",
      "baselinePercent": 0.3,
      "baselineLabel": "Code Input"
    }
  },
  "connector": {
    "label": "Both. At once.",
    "color": "rgba(255,255,255,0.6)",
    "glowBlur": 8
  },
  "callout": {
    "text": "Try it yourself. Give an LLM the same problem as code, then as natural language.",
    "width": 600,
    "height": 80
  }
}
```

---
