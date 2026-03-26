[Remotion]

# Section 4.7: Prompt-Code Spectrum — Where to Draw the Line

**Tool:** Remotion
**Duration:** ~16s (472 frames @ 30fps)
**Timestamp:** 1:36 - 1:52

## Visual Description

An animated horizontal spectrum that visualizes the continuum between pure natural language and pure code, with a slider showing where PDD recommends operating.

The spectrum is a long horizontal bar spanning most of the screen width. The LEFT end is colored blue and labeled "Pure natural language" — soft, flowing, organic. The RIGHT end is colored gray and labeled "Pure code" — sharp, precise, mechanical. The gradient between them transitions smoothly.

A slider (vertical marker with handle) sits mostly to the LEFT side of the spectrum — around the 25% mark from left. This represents the PDD philosophy: stay in prompt space as long as possible.

Along the spectrum, small notches appear at key positions:
- 10%: "Architecture" (deep in prompt space)
- 20%: "Intent & constraints" (still prompt space)
- 30%: "Edge cases" (prompt space, approaching boundary)
- 60%: "Critical algorithms" (dipping into code)
- 80%: "Performance-critical paths" (code territory)

A label below the spectrum reads: "Stay in prompt space as long as possible. Dip into code when you must."

The slider then briefly animates — it slides right to 60% (showing a "code dip") then returns to 25% — demonstrating that you dip in and come back.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- Blueprint grid: 60px spacing, `#1E293B` at 0.03

### Chart/Visual Elements

#### Spectrum Bar
- Position: centered, from x: 200 to x: 1720, at y: 480
- Height: 24px, rounded 12px ends
- Gradient: `#4A90D9` (blue, left) → `#475569` (gray, right)
  - Mid-blend around 40%: `#6B7DB0`
- Border: `#334155` at 0.2, 1px

#### Endpoint Labels
- Left: "Pure natural language" — Inter, 14px, semi-bold (600), `#4A90D9`, below-left at (200, 530)
- Right: "Pure code" — Inter, 14px, semi-bold (600), `#475569`, below-right at (1720, 530)

#### Slider
- Vertical bar: 3px wide × 48px tall, `#E2E8F0`, centered on spectrum
- Handle: 12px circle, `#E2E8F0` fill, `#4A90D9` border 2px
- Glow: `#4A90D9` at 0.2, 8px radius
- Initial position: x: 580 (~25% from left)

#### Notch Marks
- Small vertical ticks (2px × 12px) above the spectrum bar
- Each with a label:
  1. x: 352 (10%): "Architecture" — Inter, 10px, `#4A90D9` at 0.6
  2. x: 504 (20%): "Intent & constraints" — Inter, 10px, `#4A90D9` at 0.5
  3. x: 656 (30%): "Edge cases" — Inter, 10px, `#6B7DB0` at 0.5
  4. x: 1112 (60%): "Critical algorithms" — Inter, 10px, `#8B9AB0` at 0.5
  5. x: 1416 (80%): "Performance paths" — Inter, 10px, `#475569` at 0.5
- Tick color: same as label color, 1px

#### Zone Indicator
- Below the slider position, a bracket spans from 10%-30%: "PDD sweet spot" — Inter, 11px, `#2DD4BF` at 0.5
- Bracket: `#2DD4BF` at 0.3, 1px, with small serifs at ends

#### Bottom Label
- "Stay in prompt space as long as possible. Dip into code when you must." — Inter, 16px, `#94A3B8` at 0.6, centered at y: 680

### Animation Sequence
1. **Frame 0-30 (0-1s):** Spectrum bar draws in from center outward. Gradient fills.
2. **Frame 30-60 (1-2s):** Endpoint labels fade in. "Pure natural language" on left, "Pure code" on right.
3. **Frame 60-120 (2-4s):** Notch marks appear one by one from left to right, with labels. 10-frame stagger between each.
4. **Frame 120-150 (4-5s):** Slider appears at 25% position. Handle and glow animate in. Zone bracket appears: "PDD sweet spot".
5. **Frame 150-210 (5-7s):** Hold. Slider and spectrum visible together.
6. **Frame 210-270 (7-9s):** Slider slides RIGHT to 60% mark — "dipping into code." The slider's glow color shifts from blue to a neutral `#8B9AB0`.
7. **Frame 270-330 (9-11s):** Slider returns LEFT to 25% — "back in prompt space." Glow returns to blue.
8. **Frame 330-390 (11-13s):** Bottom label fades in: "Stay in prompt space as long as possible. Dip into code when you must."
9. **Frame 390-472 (13-15.7s):** Hold. The composition is stable and clear.

### Typography
- Endpoint labels: Inter, 14px, semi-bold (600), respective colors
- Notch labels: Inter, 10px, respective colors
- Zone label: Inter, 11px, `#2DD4BF` at 0.5
- Bottom label: Inter, 16px, `#94A3B8` at 0.6

### Easing
- Spectrum draw: `easeInOut(cubic)` over 30 frames, from center outward
- Label fade: `easeOut(quad)` over 20 frames
- Notch stagger: `easeOut(quad)` per notch, 10-frame stagger
- Slider appear: `spring(damping: 12)` over 20 frames
- Slider slide right: `easeInOut(cubic)` over 60 frames
- Slider slide left: `easeInOut(cubic)` over 60 frames
- Glow color shift: `easeInOut(quad)` over 30 frames
- Bottom label: `easeOut(quad)` over 20 frames

## Narration Sync
> "Think of it as a spectrum. On one end, pure natural language. On the other, pure code."
> "PDD says: stay on the natural-language side as long as possible. Describe architecture, intent, constraints, edge cases — all in plain English."
> "Then, when you hit something that genuinely needs code precision — a regex, an algorithm, a performance path — dip into code. Just for that section. Then come back."
> "This is the real shift. Not 'cheaper material.' A migration of where value lives."

Segments: `part4_precision_tradeoff_010`

- **96.14s** (seg 010): Spectrum bar draws in
- **98s**: Endpoint labels, notches appearing
- **100s**: Slider at 25%, zone bracket visible
- **103s**: Slider dips right to 60%
- **106s**: Slider returns to 25%
- **108s**: Bottom label appears
- **111.84s** (seg 010 ends): Hold, section complete

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={472}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    <BlueprintGrid spacing={60} color="#1E293B" opacity={0.03} />

    {/* Spectrum bar */}
    <Sequence from={0}>
      <DrawFromCenter duration={30}>
        <GradientBar x={200} y={468} width={1520} height={24}
          borderRadius={12}
          gradient={["#4A90D9", "#6B7DB0", "#475569"]}
          border="#334155" borderOpacity={0.2} />
      </DrawFromCenter>
    </Sequence>

    {/* Endpoint labels */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <Text text="Pure natural language" font="Inter" size={14}
          weight={600} color="#4A90D9" x={200} y={530} />
        <Text text="Pure code" font="Inter" size={14}
          weight={600} color="#475569" x={1720} y={530} align="right" />
      </FadeIn>
    </Sequence>

    {/* Notch marks with labels */}
    <Sequence from={60}>
      {[
        { x: 352, label: "Architecture", color: "#4A90D9", opacity: 0.6 },
        { x: 504, label: "Intent & constraints", color: "#4A90D9", opacity: 0.5 },
        { x: 656, label: "Edge cases", color: "#6B7DB0", opacity: 0.5 },
        { x: 1112, label: "Critical algorithms", color: "#8B9AB0", opacity: 0.5 },
        { x: 1416, label: "Performance paths", color: "#475569", opacity: 0.5 }
      ].map((notch, i) => (
        <Sequence key={i} from={i * 10}>
          <FadeIn duration={10}>
            <NotchMark x={notch.x} y={456} width={2} height={12}
              color={notch.color} opacity={notch.opacity} />
            <Text text={notch.label} font="Inter" size={10}
              color={notch.color} opacity={notch.opacity}
              x={notch.x} y={440} align="center" />
          </FadeIn>
        </Sequence>
      ))}
    </Sequence>

    {/* Slider */}
    <Sequence from={120}>
      <AnimatedSlider
        y={456} height={48} handleRadius={12}
        barColor="#E2E8F0" barWidth={3}
        handleFill="#E2E8F0" handleBorder="#4A90D9" handleBorderWidth={2}
        glowColor="#4A90D9" glowOpacity={0.2} glowRadius={8}
        keyframes={[
          { frame: 0, x: 580 },
          { frame: 90, x: 1112, glowColor: "#8B9AB0" },
          { frame: 150, x: 580, glowColor: "#4A90D9" }
        ]}
        startMove={90} />
    </Sequence>

    {/* PDD sweet spot bracket */}
    <Sequence from={120}>
      <FadeIn duration={20}>
        <Bracket x1={352} x2={656} y={510}
          color="#2DD4BF" opacity={0.3} width={1}
          label="PDD sweet spot" labelFont="Inter" labelSize={11}
          labelColor="#2DD4BF" labelOpacity={0.5} />
      </FadeIn>
    </Sequence>

    {/* Bottom label */}
    <Sequence from={330}>
      <FadeIn duration={20}>
        <Text text="Stay in prompt space as long as possible. Dip into code when you must."
          font="Inter" size={16} color="#94A3B8" opacity={0.6}
          x={960} y={680} align="center" />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "spectrum_visualization",
  "spectrum": {
    "left": { "label": "Pure natural language", "color": "#4A90D9" },
    "right": { "label": "Pure code", "color": "#475569" },
    "width": 1520
  },
  "notches": [
    { "position": 0.10, "label": "Architecture", "color": "#4A90D9" },
    { "position": 0.20, "label": "Intent & constraints", "color": "#4A90D9" },
    { "position": 0.30, "label": "Edge cases", "color": "#6B7DB0" },
    { "position": 0.60, "label": "Critical algorithms", "color": "#8B9AB0" },
    { "position": 0.80, "label": "Performance paths", "color": "#475569" }
  ],
  "slider": {
    "restPosition": 0.25,
    "dipPosition": 0.60,
    "label": "PDD sweet spot"
  },
  "bottomLabel": "Stay in prompt space as long as possible. Dip into code when you must.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_010"]
}
```

---
