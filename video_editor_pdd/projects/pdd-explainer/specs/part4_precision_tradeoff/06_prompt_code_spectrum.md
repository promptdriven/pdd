[Remotion]

# Section 4.6: Prompt-Code Spectrum — Stay in Prompt Space

**Tool:** Remotion
**Duration:** ~16s (472 frames @ 30fps)
**Timestamp:** 1:36 - 1:52

## Visual Description

A horizontal spectrum bar stretches across the screen. The left end is labeled "Pure natural language" in teal/blue. The right end is labeled "Pure code" in cool gray. The gradient transitions smoothly from teal to gray across the bar.

A slider/indicator sits on the spectrum — positioned mostly toward the left (natural language) end, at roughly the 25% mark. A few smaller notch markers appear at the 60%, 75%, and 90% positions, representing the occasional dips into code territory.

Below the spectrum, a label reads: **"Stay in prompt space as long as possible. Dip into code when you must."**

The visual message is clear: most specification work lives in prompt/NL space, with rare excursions into code for precision-critical sections.

Above the spectrum, example annotations appear at key positions:
- At ~15%: "Architecture" — "Intent" — "Constraints"
- At ~35%: "Edge cases" — "Error handling"
- At ~65%: "Algorithm choice"
- At ~85%: "Bit-level ops" — "Performance loops"

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (deep navy-black)
- No grid — clean, focused composition

### Chart/Visual Elements

#### Spectrum Bar
- Position: centered at y: 500, from x: 200 to x: 1720
- Dimensions: 1520×40px, rounded 20px (pill shape)
- Gradient fill: `#2DD4BF` (left) → `#475569` (right), with midpoint at ~60% for faster transition to gray
- Border: 1px, `#334155` at 0.2
- Subtle inner shadow for depth

#### Left Label
- "Pure natural language" — Inter, 16px, semi-bold, `#2DD4BF` at 0.8
- Position: x: 200, y: 560, left-aligned
- Small teal circle indicator (6px) at spectrum left edge

#### Right Label
- "Pure code" — Inter, 16px, semi-bold, `#475569` at 0.8
- Position: x: 1720, y: 560, right-aligned
- Small gray circle indicator (6px) at spectrum right edge

#### Main Slider
- Position: x: ~580 (25% along spectrum), y: 500
- Shape: vertical pill (12×50px), `#E2E8F0` at 0.9, rounded 6px
- Glow: `#2DD4BF` at 0.2, 15px radius
- Drop shadow: 0 2px 8px rgba(0,0,0,0.3)

#### Notch Markers
- 3 smaller indicators at 60%, 75%, 90% positions along spectrum
- Shape: vertical ticks (4×20px), `#94A3B8` at 0.4
- No glow — these are minor dips

#### Example Annotations (above spectrum)
- At ~15%: "Architecture" — Inter, 12px, `#2DD4BF` at 0.5, y: 420
- At ~25%: "Intent" — Inter, 12px, `#2DD4BF` at 0.5, y: 440
- At ~35%: "Constraints" / "Edge cases" — Inter, 12px, `#2DD4BF` at 0.45, y: 420/440
- At ~65%: "Algorithm choice" — Inter, 12px, `#94A3B8` at 0.5, y: 420
- At ~85%: "Bit-level ops" / "Perf. loops" — Inter, 12px, `#64748B` at 0.5, y: 420/440
- Thin connector lines from annotations to spectrum bar, 1px, matching color at 0.15

#### Bottom Label
- "Stay in prompt space as long as possible." — Inter, 22px, semi-bold, `#E2E8F0` at 0.8, centered at y: 680
- "Dip into code when you must." — Inter, 22px, `#94A3B8` at 0.6, centered at y: 720

#### Contextual Quote
- "The question isn't 'prompts OR code.'" — Inter, 14px, italic, `#64748B` at 0.4, centered at y: 800
- "It's 'how far into prompt space can you stay?'" — Inter, 14px, italic, `#94A3B8` at 0.5, centered at y: 825
- "For most of the specification — further than you'd think." — Inter, 14px, bold, `#2DD4BF` at 0.6, centered at y: 860

### Animation Sequence
1. **Frame 0-45 (0-1.5s):** Spectrum bar draws from center outward (expanding horizontally). Gradient fills in.
2. **Frame 45-90 (1.5-3s):** Left and right labels appear. End-point circles fade in.
3. **Frame 90-150 (3-5s):** Main slider slides in from left, settling at the 25% position with a slight overshoot-bounce. Glow pulses once.
4. **Frame 150-210 (5-7s):** Notch markers appear at 60%, 75%, 90% with subtle drop-in animation.
5. **Frame 210-300 (7-10s):** Example annotations type in above the spectrum, left to right. Connector lines draw down to spectrum bar.
6. **Frame 300-360 (10-12s):** Bottom label appears — "Stay in prompt space as long as possible." then "Dip into code when you must."
7. **Frame 360-420 (12-14s):** Contextual quote lines appear sequentially.
8. **Frame 420-472 (14-16s):** Hold. The left (NL) region of the spectrum pulses gently — most of the work lives here.

### Typography
- Spectrum labels: Inter, 16px, semi-bold (600), respective colors
- Example annotations: Inter, 12px, respective colors
- Bottom label line 1: Inter, 22px, semi-bold (600), `#E2E8F0` at 0.8
- Bottom label line 2: Inter, 22px, regular (400), `#94A3B8` at 0.6
- Contextual quote: Inter, 14px, italic/bold as specified

### Easing
- Spectrum draw: `easeInOut(cubic)` over 45 frames
- Labels fade-in: `easeOut(quad)` over 20 frames
- Slider slide-in: `easeOut(back)` over 30 frames (overshoot bounce)
- Notch drop-in: `easeOut(cubic)` over 15 frames, staggered 10 frames
- Annotation type-in: `easeOut(quad)` over 15 frames each, staggered 15 frames
- Connector draw: `easeInOut(quad)` over 10 frames
- Bottom label: `easeOut(cubic)` over 25 frames
- Quote lines: `easeOut(quad)` over 20 frames, staggered 15 frames
- NL region pulse: `easeInOut(sine)` on 50-frame cycle

## Narration Sync
> "Think of it as a spectrum. Natural language on one end, code on the other. The question isn't 'prompts OR code.' It's 'how far into prompt space can you stay?' For most of the specification — further than you'd think."

Segment: `part4_precision_tradeoff_010`

- **1:36** ("Think of it as a spectrum"): Spectrum bar draws, gradient visible
- **1:38** ("Natural language on one end"): Left label appears, slider settles into position
- **1:40** ("code on the other"): Right label appears, notch markers visible
- **1:43** ("prompts OR code"): Example annotations appearing along spectrum
- **1:46** ("how far into prompt space"): Bottom label appears — emphasis on staying left
- **1:49** ("further than you'd think"): Quote line 3 appears, NL region pulsing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={472}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>

    {/* Spectrum bar */}
    <Sequence from={0}>
      <ExpandFromCenter duration={45}>
        <SpectrumBar x={200} y={500} width={1520} height={40}
          borderRadius={20}
          gradient={["#2DD4BF", "#475569"]}
          gradientMidpoint={0.6}
          border={{ color: "#334155", opacity: 0.2, width: 1 }} />
      </ExpandFromCenter>
    </Sequence>

    {/* End labels */}
    <Sequence from={45}>
      <FadeIn duration={20}>
        <Text text="Pure natural language" font="Inter" size={16}
          weight={600} color="#2DD4BF" opacity={0.8}
          x={200} y={560} align="left" />
        <Circle cx={200} cy={500} r={6} fill="#2DD4BF" />
      </FadeIn>
      <FadeIn duration={20}>
        <Text text="Pure code" font="Inter" size={16}
          weight={600} color="#475569" opacity={0.8}
          x={1720} y={560} align="right" />
        <Circle cx={1720} cy={500} r={6} fill="#475569" />
      </FadeIn>
    </Sequence>

    {/* Main slider */}
    <Sequence from={90}>
      <SlideIn from="left" to={580} duration={30} overshoot={0.15}>
        <SliderIndicator x={580} y={500} width={12} height={50}
          color="#E2E8F0" opacity={0.9} borderRadius={6}
          glow={{ color: "#2DD4BF", opacity: 0.2, radius: 15 }}
          shadow="0 2px 8px rgba(0,0,0,0.3)" />
      </SlideIn>
    </Sequence>

    {/* Notch markers */}
    {NOTCH_POSITIONS.map((pos, i) => (
      <Sequence from={150 + i * 10} key={pos}>
        <DropIn duration={15}>
          <NotchTick x={pos} y={500} width={4} height={20}
            color="#94A3B8" opacity={0.4} />
        </DropIn>
      </Sequence>
    ))}

    {/* Example annotations */}
    {ANNOTATIONS.map((ann, i) => (
      <Sequence from={210 + i * 15} key={ann.label}>
        <FadeIn duration={15}>
          <AnnotationLabel text={ann.label} x={ann.x} y={ann.y}
            font="Inter" size={12} color={ann.color} opacity={ann.opacity} />
          <ConnectorLine from={[ann.x, ann.y + 15]} to={[ann.x, 480]}
            color={ann.color} opacity={0.15} width={1} />
        </FadeIn>
      </Sequence>
    ))}

    {/* Bottom label */}
    <Sequence from={300}>
      <FadeIn duration={25}>
        <Text text="Stay in prompt space as long as possible."
          font="Inter" size={22} weight={600}
          color="#E2E8F0" opacity={0.8}
          x={960} y={680} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <FadeIn duration={25}>
          <Text text="Dip into code when you must."
            font="Inter" size={22} weight={400}
            color="#94A3B8" opacity={0.6}
            x={960} y={720} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Contextual quote */}
    <Sequence from={360}>
      <FadeIn duration={20}>
        <Text text="The question isn't 'prompts OR code.'"
          font="Inter" size={14} style="italic"
          color="#64748B" opacity={0.4}
          x={960} y={800} align="center" />
      </FadeIn>
      <Sequence from={15}>
        <FadeIn duration={20}>
          <Text text="It's 'how far into prompt space can you stay?'"
            font="Inter" size={14} style="italic"
            color="#94A3B8" opacity={0.5}
            x={960} y={825} align="center" />
        </FadeIn>
      </Sequence>
      <Sequence from={30}>
        <FadeIn duration={20}>
          <Text text="For most of the specification — further than you'd think."
            font="Inter" size={14} weight={700}
            color="#2DD4BF" opacity={0.6}
            x={960} y={860} align="center" />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* NL region pulse */}
    <Sequence from={420}>
      <GlowPulse region={{ x: 200, width: 500 }} color="#2DD4BF"
        opacity={0.06} cycle={50} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_diagram",
  "diagramId": "prompt_code_spectrum",
  "spectrum": {
    "leftEnd": { "label": "Pure natural language", "color": "#2DD4BF" },
    "rightEnd": { "label": "Pure code", "color": "#475569" },
    "width": 1520
  },
  "slider": {
    "position": 0.25,
    "label": "Most work lives here"
  },
  "notches": [
    { "position": 0.60, "label": "Algorithm choice" },
    { "position": 0.75, "label": "Bit-level ops" },
    { "position": 0.90, "label": "Performance loops" }
  ],
  "annotations": [
    { "position": 0.15, "label": "Architecture", "color": "#2DD4BF" },
    { "position": 0.25, "label": "Intent", "color": "#2DD4BF" },
    { "position": 0.35, "label": "Constraints / Edge cases", "color": "#2DD4BF" },
    { "position": 0.65, "label": "Algorithm choice", "color": "#94A3B8" },
    { "position": 0.85, "label": "Bit-level ops / Perf. loops", "color": "#64748B" }
  ],
  "bottomLabel": {
    "line1": "Stay in prompt space as long as possible.",
    "line2": "Dip into code when you must."
  },
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_precision_tradeoff_010"]
}
```

---
