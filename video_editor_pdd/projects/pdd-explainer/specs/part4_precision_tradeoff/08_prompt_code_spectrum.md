[Remotion]

# Section 4.7: Prompt–Code Spectrum — Stay in Prompt Space

**Tool:** Remotion
**Duration:** ~16s (480 frames @ 30fps)
**Timestamp:** 1:22 – 1:38

## Visual Description
A horizontal spectrum bar stretches across the screen with "Pure natural language" on the left (blue) and "Pure code" on the right (gray). A slider dot sits at approximately 25% from the left — PDD's sweet spot. A bracket labeled "PDD Zone" marks the 10–35% range where most specification happens. The slider briefly hops to notch marks at 60%, 75%, and 90% (representing rare code-level precision needs) before returning to the PDD zone. Below the spectrum, a concluding text reframes the question: "The question isn't prompts OR code. It's how far into prompt space can you stay?" The animation makes the fluid boundary tangible.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #0F172A (dark navy)
- No grid lines

### Chart/Visual Elements
- **Spectrum bar:** 1200px wide × 40px tall, centered at (960, 440)
  - Left gradient: `#4A90D9` (blue, natural language)
  - Right gradient: `#6B7C93` (gray, code)
  - Gradient transition: smooth linear blend across full width
  - Rounded ends: 20px radius
  - Border: 1px, `rgba(255,255,255,0.1)`
- **Left label:** "Pure natural language" — `#4A90D9`, 16px, positioned at left end (360, 400)
- **Right label:** "Pure code" — `#6B7C93`, 16px, positioned at right end (1560, 400)
- **Slider dot:** 16px circle, `#FFFFFF` with 3px glow halo, positioned at 25% from left (x≈660)
- **PDD Zone bracket:** Spans 10%–35% of bar (x: 480–780)
  - Top bracket line: 2px, `#FFFFFF` at 0.3 opacity, with downward ticks at ends
  - Label: "PDD Zone" — `#FFFFFF` at 0.6 opacity, 14px, centered above bracket at y=390
  - Subtle fill highlight: `rgba(74,144,217,0.06)` behind PDD zone section of spectrum
- **Code notch marks:** Small ticks on the spectrum bar at 60%, 75%, 90%
  - 60%: Label "Algorithm choice" — `#94A3B8`, 11px, below bar
  - 75%: Label "Inner loops" — `#94A3B8`, 11px
  - 90%: Label "Bit ops" — `#94A3B8`, 11px
  - Each notch: 2px wide × 12px tall tick, `#D9944A` at 0.4 opacity
- **Concluding text:** Two lines, centered at (960, 640):
  - Line 1: "The question isn't "prompts OR code."" — `#FFFFFF` at 0.6 opacity, 22px
  - Line 2: "It's "how far into prompt space can you stay?"" — `#FFFFFF` at 0.8 opacity, 22px, bold
- **Answer text:** "For most of the specification — further than you'd think." — centered at (960, 720), `#4A90D9` at 0.7 opacity, 18px

### Animation Sequence
1. **Frame 0–40 (0–1.33s):** Spectrum bar draws in from center outward — left half extends left (turning blue), right half extends right (turning gray). End labels fade in.
2. **Frame 40–80 (1.33–2.67s):** PDD Zone bracket draws in — top line extends, ticks drop down, "PDD Zone" label fades in. Slider dot appears at 25% position with a pop-in spring animation and glow pulse.
3. **Frame 80–140 (2.67–4.67s):** Code notch marks appear at 60%, 75%, 90% with 10-frame stagger. Each tick drops down with their labels fading in below. These represent the exceptions — rare code needs.
4. **Frame 140–200 (4.67–6.67s):** Slider dot hops to 60% notch (algorithm choice) — pauses 15 frames — hops to 75% (inner loops) — pauses 10 frames — hops to 90% (bit ops) — pauses 10 frames. Each hop is a quick `easeInOutBack` with subtle trail.
5. **Frame 200–250 (6.67–8.33s):** Slider dot returns to PDD Zone (25%) with a satisfying snap. A brief pulse on the PDD Zone fill emphasizes "this is home." The notch labels dim to 0.2 opacity — they're exceptions, not the norm.
6. **Frame 250–340 (8.33–11.33s):** Concluding text appears — Line 1 fades in, then 500ms later Line 2 fades in with slight upward drift and bold emphasis on "how far into prompt space can you stay?"
7. **Frame 340–420 (11.33–14.0s):** Answer text fades in: "For most of the specification — further than you'd think." in blue.
8. **Frame 420–480 (14.0–16.0s):** Hold. Slider breathes with gentle glow. PDD Zone has ambient pulse.

### Typography
- End labels: Inter Medium, 16px, respective colors
- PDD Zone label: Inter SemiBold, 14px, `#FFFFFF` at 0.6 opacity
- Notch labels: Inter Regular, 11px, `#94A3B8`
- Concluding Line 1: Inter Regular, 22px, `#FFFFFF` at 0.6 opacity
- Concluding Line 2: Inter Bold, 22px, `#FFFFFF` at 0.8 opacity
- Answer text: Inter Medium, 18px, `#4A90D9` at 0.7 opacity

### Easing
- Spectrum draw: `easeOutCubic`
- Slider pop-in: `spring({ damping: 10, stiffness: 140 })`
- Notch appear: `easeOutQuad`
- Slider hop: `easeInOutBack` (overshoot gives playful energy)
- Slider return: `spring({ damping: 14, stiffness: 120 })`
- Concluding text fade: `easeOutCubic`
- Answer text fade: `easeOutQuad`
- Breathing glow: `easeInOutSine` (2s cycle)

## Narration Sync
> "Think of it as a spectrum. Natural language on one end, code on the other."

> "The question isn't prompts or code. It's how far into prompt space can you stay? For most of the specification, further than you'd think."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={480}>
  <AbsoluteFill style={{ backgroundColor: '#0F172A' }}>
    {/* Spectrum bar */}
    <Sequence from={0} durationInFrames={40}>
      <SpectrumBar
        width={1200}
        height={40}
        leftColor="#4A90D9"
        rightColor="#6B7C93"
        leftLabel="Pure natural language"
        rightLabel="Pure code"
        y={440}
      />
    </Sequence>

    {/* PDD Zone bracket + slider */}
    <Sequence from={40} durationInFrames={40}>
      <ZoneBracket
        range={[0.10, 0.35]}
        label="PDD Zone"
        fillColor="rgba(74,144,217,0.06)"
        y={440}
      />
      <SliderDot position={0.25} y={440} />
    </Sequence>

    {/* Code notch marks */}
    <Sequence from={80} durationInFrames={60}>
      <NotchMarks
        positions={[
          { at: 0.60, label: "Algorithm choice" },
          { at: 0.75, label: "Inner loops" },
          { at: 0.90, label: "Bit ops" },
        ]}
        stagger={10}
        color="#D9944A"
        y={440}
      />
    </Sequence>

    {/* Slider hops to notches */}
    <Sequence from={140} durationInFrames={60}>
      <AnimatedSlider
        keyframes={[
          { position: 0.25, hold: 0 },
          { position: 0.60, hold: 15 },
          { position: 0.75, hold: 10 },
          { position: 0.90, hold: 10 },
        ]}
        y={440}
      />
    </Sequence>

    {/* Slider returns to PDD zone */}
    <Sequence from={200} durationInFrames={50}>
      <AnimatedSlider
        keyframes={[{ position: 0.90, hold: 0 }, { position: 0.25, hold: 30 }]}
        y={440}
      />
      <ZonePulse range={[0.10, 0.35]} />
    </Sequence>

    {/* Concluding text */}
    <Sequence from={250} durationInFrames={90}>
      <FadeIn>
        <CenterText
          text='The question isn't "prompts OR code."'
          y={620}
          size={22}
          opacity={0.6}
        />
      </FadeIn>
      <Sequence from={15}>
        <FadeIn yDrift={6}>
          <CenterText
            text='"How far into prompt space can you stay?"'
            y={660}
            size={22}
            bold={true}
            opacity={0.8}
          />
        </FadeIn>
      </Sequence>
    </Sequence>

    {/* Answer text */}
    <Sequence from={340} durationInFrames={80}>
      <FadeIn>
        <CenterText
          text="For most of the specification — further than you'd think."
          y={720}
          size={18}
          color="#4A90D9"
          opacity={0.7}
        />
      </FadeIn>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "backgroundColor": "#0F172A",
  "spectrum": {
    "width": 1200,
    "height": 40,
    "leftColor": "#4A90D9",
    "leftLabel": "Pure natural language",
    "rightColor": "#6B7C93",
    "rightLabel": "Pure code",
    "y": 440
  },
  "pddZone": {
    "range": [0.10, 0.35],
    "label": "PDD Zone",
    "sliderPosition": 0.25,
    "fillColor": "rgba(74,144,217,0.06)"
  },
  "codeNotches": [
    { "position": 0.60, "label": "Algorithm choice" },
    { "position": 0.75, "label": "Inner loops" },
    { "position": 0.90, "label": "Bit ops" }
  ],
  "concludingText": {
    "line1": "The question isn't \"prompts OR code.\"",
    "line2": "\"How far into prompt space can you stay?\"",
    "answer": "For most of the specification — further than you'd think."
  }
}
```

---
