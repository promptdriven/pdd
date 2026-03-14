[Remotion]

# Section 2.7: Narration Overlay Intro

**Tool:** Remotion
**Duration:** ~0.8s
**Timestamp:** 0:15 – 0:15.8

## Visual Description
A narration-synced text overlay composited over a blurred still from the Veo footage. The spoken narration text appears as an animated subtitle/quote at the center of the screen, with a waveform visualizer bar running beneath it to represent the audio track. The text types in word-by-word in sync with the narration cadence. A thin accent underline grows beneath the text as it completes. This component demonstrates how narration integrates with Veo footage in the pipeline.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Blurred Veo footage still (Gaussian blur 20px) with dark overlay #0B1120 at 50% opacity
- No grid lines

### Chart/Visual Elements
- **Narration text block (center, y: 440):**
  - Text: "Veo-generated clips with narration overlay"
  - Max width: 900px, centered horizontally
  - Each word appears sequentially with a slight fade-up
- **Waveform bar (center, y: 560):**
  - 40 vertical bars, each 4px wide, spaced 6px apart, total width ~400px, centered
  - Bar heights: randomized 10–40px, color #4FC3F7 at 80% opacity
  - Bars pulse in a traveling wave pattern left-to-right
- **Accent underline (y: 530):**
  - 2px solid line, #C9A84C (gold), max width matching text block width
  - Animates from center outward

### Animation Sequence
1. **Frame 0–4 (0–0.13s):** Background blur and overlay fade in (opacity 0→1)
2. **Frame 4–18 (0.13–0.6s):** Words appear one at a time (~2.3 frames per word for 6 words). Each word: opacity 0→1, translateY +8→0
3. **Frame 10–20 (0.33–0.67s):** Waveform bars begin pulsing (traveling wave, amplitude oscillates)
4. **Frame 18–22 (0.6–0.73s):** Accent underline grows from width 0 → full text width, centered
5. **Frame 22–24 (0.73–0.8s):** Hold — all visible, waveform continues subtle pulse

### Typography
- Narration text: Inter Medium, 40px, white (#FFFFFF), line-height 1.4
- No additional labels

### Easing
- Word fade-in: `easeOutCubic`
- Waveform pulse: `sinusoidal` (continuous oscillation)
- Underline grow: `easeInOutQuad`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={24}>
  <AbsoluteFill>
    <BlurredBackground src="/veo/ocean_wave_sunset_still.jpg" blur={20} overlayOpacity={0.5} />

    <Sequence from={4}>
      <WordByWordText
        text="Veo-generated clips with narration overlay"
        framesPerWord={2.3}
        fontSize={40}
        color="#FFFFFF"
        y={440}
      />
    </Sequence>

    <Sequence from={10}>
      <WaveformVisualizer
        barCount={40}
        barWidth={4}
        barGap={6}
        color="#4FC3F7"
        y={560}
      />
    </Sequence>

    <Sequence from={18}>
      <AccentUnderline color="#C9A84C" width={580} y={530} />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "narration_text": "Veo-generated clips with narration overlay",
  "word_count": 6,
  "waveform_bars": 40,
  "accent_color": "#C9A84C",
  "background_source": "ocean_wave_sunset_still.jpg"
}
```

---
