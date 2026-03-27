[Remotion]

# Section 4.9: Prompt–Code Spectrum with Slider

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 1:32 - 1:48

## Visual Description

A horizontal spectrum/slider visualization showing the continuum between natural language and code. This is the closing conceptual visual of Part 4 — reframing the question from "prompts OR code" to "how far into prompt space can you stay?"

**The Spectrum Bar:** A wide horizontal gradient bar spanning most of the canvas width. LEFT end is blue (`#4A90D9`) labeled "Pure natural language". RIGHT end is gray (`#64748B`) labeled "Pure code". The gradient transitions smoothly between the two.

**The Slider:** A marker/thumb sits on the spectrum, positioned mostly toward the left (natural language) side — roughly 20-25% from the left edge. It has a white dot with a soft glow. This represents the typical PDD sweet spot — mostly natural language with occasional dips into code.

**Notch Marks:** Along the spectrum, 3-4 small notch marks sit at various positions toward the right side of the slider, representing the "dips into code" — algorithm specs, performance-critical sections. These are small, discrete — most of the specification stays left.

**Label:** Below the spectrum: "Stay in prompt space as long as possible. Dip into code when you must." This is the closing thesis.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)

### Chart/Visual Elements

#### Spectrum Bar
- Position: x: 160 to 1760, y: 460, height: 40px, rounded 20px (pill shape)
- Gradient: `#4A90D9` (left) → `#2A3A5A` (middle) → `#64748B` (right)
- Border: `#334155`, 1px
- Width: 1600px

#### Endpoint Labels
- Left: "Pure natural language" — Inter, 16px, semi-bold (600), `#4A90D9`, above bar at x: 160
- Right: "Pure code" — Inter, 16px, semi-bold (600), `#64748B`, above bar at x: 1760, right-aligned

#### Slider / Thumb
- Position: x: ~480 (20% from left)
- Shape: 20px white circle, `#E2E8F0`
- Glow: `#FFFFFF` at 0.15, 16px blur
- Drop shadow: `#000000` at 0.3, 4px blur, 2px offset

#### Notch Marks
- 4 small vertical ticks at x: ~900, ~1100, ~1300, ~1500
- Size: 4×16px each, `#94A3B8` at 0.4
- Each notch: a "dip into code" — small but visible
- Notch labels (very small): "algorithm", "hash fn", "bit ops", "perf loop" — Inter, 9px, `#64748B` at 0.3, below spectrum

#### Zone Indicator
- Left of slider: filled overlay `#4A90D9` at 0.08 — "prompt space"
- Right of slider: no overlay — "code space"

#### Bottom Label
- "Stay in prompt space as long as possible." — Inter, 22px, `#E2E8F0`, centered at y: 600
- "Dip into code when you must." — Inter, 22px, `#94A3B8`, centered at y: 640

### Animation Sequence
1. **Frame 0-60 (0-2s):** Spectrum bar draws in from center outward. Endpoint labels fade in.
2. **Frame 60-150 (2-5s):** Slider appears at the left end, then slides rightward to its resting position (~20%). The zone indicator fills behind it as it moves. The slider "settling" gesture emphasizes that it sits mostly in prompt space.
3. **Frame 150-270 (5-9s):** Notch marks appear one by one along the right portion — each with a tiny pop animation. These are the code dips. Their small size reinforces their rarity.
4. **Frame 270-360 (9-12s):** Bottom label fades in, line by line. "Stay in prompt space as long as possible." then "Dip into code when you must."
5. **Frame 360-450 (12-15s):** Hold. The spectrum tells the whole story.
6. **Frame 450-480 (15-16s):** Gentle fade to black.

### Typography
- Endpoint labels: Inter, 16px, semi-bold (600), respective colors
- Notch labels: Inter, 9px, regular (400), `#64748B` at 0.3
- Bottom primary: Inter, 22px, regular (400), `#E2E8F0`
- Bottom secondary: Inter, 22px, regular (400), `#94A3B8`

### Easing
- Bar draw: `easeOut(cubic)` over 40 frames
- Endpoint labels: `easeOut(quad)` over 20 frames
- Slider slide: `easeInOut(cubic)` over 60 frames, with `easeOut(elastic)` settle at end (subtle bounce 1.02→1.0)
- Zone fill: tracks slider position linearly
- Notch pop: `easeOut(back)` scale 0→1 over 10 frames, staggered by 20 frames
- Bottom text: `easeOut(quad)` fade over 25 frames
- Final fade: `easeIn(quad)` over 30 frames

## Narration Sync
> "Think of it as a spectrum. Natural language on one end, code on the other. The question isn't 'prompts OR code.' It's 'how far into prompt space can you stay?' For most of the specification — further than you'd think."

Segment: `part4_precision_tradeoff_005`

- **92.54s** (seg 005): Spectrum bar begins drawing — "Think of it as a spectrum"
- **96.00s**: Slider appears and moves — "Natural language on one end, code on the other"
- **100.00s**: Notches appearing — "The question isn't prompts OR code"
- **104.00s**: Bottom label — "how far into prompt space can you stay?"
- **108.30s** (seg 005 ends): Hold — "further than you'd think"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Spectrum bar */}
    <Sequence from={0}>
      <DrawFromCenter duration={40}>
        <SpectrumBar
          x={160} y={460} width={1600} height={40}
          leftColor="#4A90D9" rightColor="#64748B"
          borderColor="#334155" borderRadius={20}
        />
      </DrawFromCenter>
    </Sequence>

    {/* Endpoint labels */}
    <Sequence from={30}>
      <FadeIn duration={20}>
        <Text text="Pure natural language"
          font="Inter" size={16} weight={600}
          color="#4A90D9" x={160} y={430} />
        <Text text="Pure code"
          font="Inter" size={16} weight={600}
          color="#64748B" x={1760} y={430} align="right" />
      </FadeIn>
    </Sequence>

    {/* Zone fill */}
    <Sequence from={60}>
      <ZoneFill
        x={160} y={460} height={40}
        color="#4A90D9" opacity={0.08}
        widthTarget={320} duration={60}
        borderRadius={20}
      />
    </Sequence>

    {/* Slider */}
    <Sequence from={60}>
      <SliderThumb
        startX={160} endX={480}
        y={480} size={20}
        color="#E2E8F0"
        glowColor="#FFFFFF" glowOpacity={0.15}
        slideDuration={60}
        settleEasing="easeOutElastic"
      />
    </Sequence>

    {/* Notch marks */}
    <Sequence from={150}>
      {notchPositions.map((pos, i) => (
        <Sequence key={i} from={i * 20}>
          <PopIn duration={10}>
            <NotchMark x={pos.x} y={460}
              width={4} height={16}
              color="#94A3B8" opacity={0.4}
              label={pos.label}
              labelColor="#64748B" labelOpacity={0.3}
            />
          </PopIn>
        </Sequence>
      ))}
    </Sequence>

    {/* Bottom labels */}
    <Sequence from={270}>
      <FadeIn duration={25}>
        <Text text="Stay in prompt space as long as possible."
          font="Inter" size={22} color="#E2E8F0"
          x={960} y={600} align="center" />
      </FadeIn>
    </Sequence>
    <Sequence from={300}>
      <FadeIn duration={25}>
        <Text text="Dip into code when you must."
          font="Inter" size={22} color="#94A3B8"
          x={960} y={640} align="center" />
      </FadeIn>
    </Sequence>

    {/* Fade out */}
    <Sequence from={450}>
      <FadeOut duration={30} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "spectrum_slider",
  "chartId": "prompt_code_spectrum",
  "spectrum": {
    "leftLabel": "Pure natural language",
    "leftColor": "#4A90D9",
    "rightLabel": "Pure code",
    "rightColor": "#64748B",
    "width": 1600
  },
  "slider": {
    "position": 0.20,
    "label": "Typical PDD sweet spot"
  },
  "notches": [
    { "position": 0.46, "label": "algorithm" },
    { "position": 0.59, "label": "hash fn" },
    { "position": 0.71, "label": "bit ops" },
    { "position": 0.84, "label": "perf loop" }
  ],
  "insight": {
    "primary": "Stay in prompt space as long as possible.",
    "secondary": "Dip into code when you must."
  },
  "narrationSegments": ["part4_precision_tradeoff_005"]
}
```

---
