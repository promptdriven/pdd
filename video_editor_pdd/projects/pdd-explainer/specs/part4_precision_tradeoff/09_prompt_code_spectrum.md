[Remotion]

# Section 4.9: Prompt-Code Spectrum — Stay in Prompt Space

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 20:00 - 20:16

## Visual Description

A horizontal spectrum bar spans the full width of the screen. The LEFT end is labeled "Pure natural language" and glows soft blue (`#4A90D9`). The RIGHT end is labeled "Pure code" and glows cool gray (`#64748B`). The spectrum transitions smoothly between the two colors.

A slider marker sits on the spectrum — positioned about 25% from the left. It's mostly in "prompt space" with a few notches toward the right. Below the spectrum, category labels show what lives where along the range:

- Far left (blue zone): "Architecture" / "Intent" / "Constraints"
- Center-left: "Edge cases" / "Error philosophy"
- Center-right: "Algorithm choice" / "Data structures"
- Far right (gray zone): "Inner loops" / "Bit operations"

The slider has a glowing indicator that pulses, and a caption reads: "Stay in prompt space as long as possible. Dip into code when you must."

The key animation: the slider starts at the far left and considers moving right. It inches rightward tentatively, then pulls back. It moves right again past "Edge cases" — no, that can stay as prompt. It only commits to moving right at "Algorithm choice" and "Inner loops" — those genuinely need code. The final position is ~25% from the left, showing that most specification stays in natural language.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: `#0A0F1A` (near-black navy)
- No grid — clean, focused layout

### Chart/Visual Elements

#### Spectrum Bar
- Position: x: 160-1760, y: 420, height: 40px, rounded ends (20px radius)
- Gradient fill: `#4A90D9` (left) → `#2A5A8A` (center-left) → `#475569` (center) → `#64748B` (right)
- Border: 1px, `#334155` at 0.3
- Left glow: `#4A90D9` at 0.1, 20px blur from left end
- Right glow: `#64748B` at 0.1, 20px blur from right end

#### End Labels
- LEFT: "Pure natural language" — Inter, 14px, semi-bold (600), `#4A90D9` at 0.7, at (160, 380)
- RIGHT: "Pure code" — Inter, 14px, semi-bold (600), `#64748B` at 0.7, at (1760, 380), right-aligned

#### Slider Marker
- Shape: inverted triangle (12px wide, 18px tall) pointing down at spectrum + circle (8px) on the spectrum
- Color: `#E2E8F0` at 0.9
- Glow: 15px blur, `#E2E8F0` at 0.2
- Final position: ~25% from left (x: ~560)

#### Category Labels (below spectrum)
- Positioned at y: 500-540, staggered vertically
- Each label has a thin leader line (1px, `#334155` at 0.2) connecting to its position on the spectrum

- **"Architecture"** — Inter, 12px, `#4A90D9` at 0.6, at x: 220
- **"Intent"** — Inter, 12px, `#4A90D9` at 0.6, at x: 380
- **"Constraints"** — Inter, 12px, `#4A90D9` at 0.55, at x: 540
- **"Edge cases"** — Inter, 12px, `#3B7AC0` at 0.5, at x: 720
- **"Error philosophy"** — Inter, 12px, `#3B7AC0` at 0.5, at x: 900
- **"Algorithm choice"** — Inter, 12px, `#64748B` at 0.5, at x: 1120
- **"Data structures"** — Inter, 12px, `#64748B` at 0.5, at x: 1320
- **"Inner loops"** — Inter, 12px, `#64748B` at 0.45, at x: 1520
- **"Bit operations"** — Inter, 12px, `#64748B` at 0.4, at x: 1700

#### Zone Indicators
- Blue zone (prompt space): faint background highlight, `#4A90D9` at 0.03, covering left ~60% of spectrum
  - Label above: "PROMPT SPACE" — Inter, 10px, `#4A90D9` at 0.25, letter-spacing 3px
- Gray zone (code space): faint background highlight, `#64748B` at 0.03, covering right ~40%
  - Label above: "CODE SPACE" — Inter, 10px, `#64748B` at 0.25, letter-spacing 3px

#### Caption
- "Stay in prompt space as long as possible. Dip into code when you must." — Inter, 16px, `#E2E8F0` at 0.5, centered at y: 700
- "prompt space" highlighted: `#4A90D9` at 0.8
- "code" highlighted: `#64748B` at 0.8

#### Decision Notches
- Small tick marks on the spectrum where decisions are made
- At "Algorithm choice" position: tick mark, `#D9944A` at 0.3, 6px tall
- At "Inner loops" position: tick mark, `#D9944A` at 0.3, 6px tall
- These are the boundaries where you "dip into code"

### Animation Sequence
1. **Frame 0-40 (0-1.33s):** Spectrum bar draws from left to right. Gradient fills in. End labels appear.
2. **Frame 40-80 (1.33-2.67s):** Zone labels fade in ("PROMPT SPACE" / "CODE SPACE"). Zone highlights appear.
3. **Frame 80-140 (2.67-4.67s):** Category labels appear from left to right, staggered by 8 frames each. Leader lines draw down to spectrum.
4. **Frame 140-200 (4.67-6.67s):** Slider appears at far left. Begins inching rightward. Passes "Architecture" — stays blue. Passes "Intent" — still blue.
5. **Frame 200-260 (6.67-8.67s):** Slider reaches "Constraints" — hesitates briefly (pauses 10 frames). Continues past "Edge cases" — passes through, still in prompt space. Reaches "Error philosophy" — brief pause.
6. **Frame 260-320 (8.67-10.67s):** Slider approaches the boundary. Decision notches flash amber at "Algorithm choice." Slider tentatively crosses, then pulls back slightly. It settles at ~25% from left — most specification stays in prompt space.
7. **Frame 320-380 (10.67-12.67s):** Caption appears below: "Stay in prompt space as long as possible. Dip into code when you must." Highlighted words glow.
8. **Frame 380-420 (12.67-14s):** Final position emphasized. A thin vertical line drops from slider to the spectrum, labeling the sweet spot. Categories in the blue zone glow slightly brighter.
9. **Frame 420-480 (14-16s):** Hold. Slider pulses. The spectrum breathes. The message is clear: most of your specification should be natural language.

### Typography
- End labels: Inter, 14px, semi-bold (600), respective colors at 0.7
- Category labels: Inter, 12px, gradient from `#4A90D9` (left) to `#64748B` (right), 0.4-0.6 opacity
- Zone labels: Inter, 10px, respective colors at 0.25, letter-spacing 3px
- Caption: Inter, 16px, `#E2E8F0` at 0.5

### Easing
- Spectrum draw: `easeInOut(cubic)` over 30 frames
- Label stagger: `easeOut(quad)` per label, 8 frame gap
- Slider movement: `easeInOut(cubic)` for main travel, `easeOut(back(1.2))` for hesitations
- Slider pullback: `easeIn(quad)` over 15 frames
- Decision notch flash: `easeOut(expo)` over 8 frames
- Caption fade: `easeOut(quad)` over 20 frames
- Slider pulse: `easeInOut(sine)` on 40-frame cycle

## Narration Sync
> "Think of it as a spectrum. Natural language on one end, code on the other. The question isn't 'prompts OR code.' It's 'how far into prompt space can you stay?' For most of the specification — further than you'd think."

Segment: `part4_009`

- **20:00** ("Think of it as a spectrum"): Spectrum bar drawing, end labels visible
- **20:04** ("Natural language on one end, code on the other"): Category labels appearing
- **20:08** ("The question isn't 'prompts OR code.'"): Slider moving along spectrum
- **20:12** ("how far into prompt space can you stay?"): Slider settling at 25% from left
- **20:15** ("further than you'd think"): Caption visible, blue zone glowing

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0A0F1A' }}>
    {/* Spectrum bar */}
    <Sequence from={0}>
      <SpectrumBar x={160} y={420} width={1600} height={40}
        leftColor="#4A90D9" rightColor="#64748B"
        borderColor="#334155" borderRadius={20}
        drawDuration={30}
        leftGlow={{ color: "#4A90D9", radius: 20, opacity: 0.1 }}
        rightGlow={{ color: "#64748B", radius: 20, opacity: 0.1 }} />
    </Sequence>

    {/* End labels */}
    <Sequence from={30}>
      <FadeIn duration={15}>
        <Text text="Pure natural language" font="Inter" size={14}
          weight={600} color="#4A90D9" opacity={0.7}
          x={160} y={380} align="left" />
        <Text text="Pure code" font="Inter" size={14}
          weight={600} color="#64748B" opacity={0.7}
          x={1760} y={380} align="right" />
      </FadeIn>
    </Sequence>

    {/* Zone labels and highlights */}
    <Sequence from={40}>
      <ZoneHighlight
        leftZone={{ x: 160, width: 960, color: "#4A90D9", label: "PROMPT SPACE" }}
        rightZone={{ x: 1120, width: 640, color: "#64748B", label: "CODE SPACE" }}
        opacity={0.03} labelOpacity={0.25}
        fadeDuration={20} />
    </Sequence>

    {/* Category labels with leader lines */}
    <Sequence from={80}>
      <StaggeredLabels
        labels={categoryLabels}
        y={500} leaderLineColor="#334155"
        stagger={8} fadeDuration={12} />
    </Sequence>

    {/* Animated slider */}
    <Sequence from={140}>
      <SpectrumSlider
        spectrumX={160} spectrumWidth={1600}
        startPosition={0} finalPosition={0.25}
        markerSize={12} markerColor="#E2E8F0"
        glowRadius={15} glowOpacity={0.2}
        path={[
          { position: 0, duration: 15 },
          { position: 0.1, duration: 15 },
          { position: 0.2, duration: 15 },
          { position: 0.3, duration: 15, pause: 10 },
          { position: 0.38, duration: 15, pause: 8 },
          { position: 0.35, duration: 10 },
          { position: 0.25, duration: 20 }
        ]}
        decisionNotches={[
          { position: 0.6, color: "#D9944A" },
          { position: 0.85, color: "#D9944A" }
        ]} />
    </Sequence>

    {/* Caption */}
    <Sequence from={320}>
      <FadeIn duration={20}>
        <HighlightedText
          text="Stay in prompt space as long as possible. Dip into code when you must."
          font="Inter" size={16} baseColor="#E2E8F0"
          baseOpacity={0.5} x={960} y={700} align="center"
          highlights={[
            { phrase: "prompt space", color: "#4A90D9", opacity: 0.8 },
            { phrase: "code", color: "#64748B", opacity: 0.8 }
          ]} />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points JSON
```json
{
  "type": "animated_spectrum",
  "spectrumId": "prompt_code_spectrum",
  "leftEnd": { "label": "Pure natural language", "color": "#4A90D9" },
  "rightEnd": { "label": "Pure code", "color": "#64748B" },
  "categories": [
    { "label": "Architecture", "position": 0.04, "zone": "prompt" },
    { "label": "Intent", "position": 0.14, "zone": "prompt" },
    { "label": "Constraints", "position": 0.24, "zone": "prompt" },
    { "label": "Edge cases", "position": 0.35, "zone": "prompt" },
    { "label": "Error philosophy", "position": 0.46, "zone": "prompt" },
    { "label": "Algorithm choice", "position": 0.60, "zone": "code" },
    { "label": "Data structures", "position": 0.73, "zone": "code" },
    { "label": "Inner loops", "position": 0.85, "zone": "code" },
    { "label": "Bit operations", "position": 0.96, "zone": "code" }
  ],
  "sliderFinalPosition": 0.25,
  "zones": [
    { "name": "PROMPT SPACE", "range": [0, 0.6], "color": "#4A90D9" },
    { "name": "CODE SPACE", "range": [0.6, 1.0], "color": "#64748B" }
  ],
  "caption": "Stay in prompt space as long as possible. Dip into code when you must.",
  "backgroundColor": "#0A0F1A",
  "narrationSegments": ["part4_009"]
}
```

---
