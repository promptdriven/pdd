[Remotion]

# Section 2.7: Narration Overlay Intro

**Tool:** Remotion
**Duration:** ~1.3s
**Timestamp:** 0:05 - 0:06

## Visual Description
A stylized demonstration of the narration overlay system. The screen shows a waveform visualization representing the TTS audio, rendered as an animated audio spectrogram/waveform bar chart across the bottom third of the screen. Above it, narration text appears word-by-word in a teleprompter-style reveal. The background is a slow-moving gradient mesh of deep blues and teals. A small "TTS: Qwen3 — Aiden" label appears in the top-right corner, identifying the voice engine. This visual demonstrates how the pipeline layers narration audio onto Veo footage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Animated gradient mesh — colors cycle between #0A1628, #1B3A5C, #0D4D4D
- No grid lines

### Chart/Visual Elements
- **Waveform visualization:**
  - 64 vertical bars spanning x=100 to x=1820, y=680 to y=980
  - Bar width: 20px with 6px gap
  - Bar heights: Randomized between 20px and 280px, animated per frame
  - Bar color: Gradient from #4DA8DA (bottom) to #8EC8E8 (top), opacity 0.7
  - Reflection: Mirrored bars below baseline at y=700, opacity 0.15
- **Narration text block:**
  - Positioned at center (960, 400), max-width 1200px
  - Current word highlighted in #FFFFFF, previous words in rgba(255,255,255,0.4)
  - Text: "It uses Veo-generated clips with narration overlay."
- **Voice engine badge:**
  - Position: top-right (1680, 40), pill shape
  - Background: rgba(77,168,218,0.2), border 1px solid #4DA8DA
  - Text: "TTS: Qwen3 — Aiden"

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Gradient mesh fades in. Voice engine badge slides in from right (translateX 40 → 0).
2. **Frame 6-10 (0.2-0.33s):** Waveform bars begin animating — heights oscillate with pseudo-random values seeded per frame.
3. **Frame 6-34 (0.2-1.13s):** Narration text reveals word-by-word. Each word fades from dim (0.4) to bright (1.0) as the "playhead" advances. Approximately 1 word per 5 frames.
4. **Frame 34-38 (1.13-1.27s):** All narration text fully visible. Waveform bars reduce to minimal heights, simulating audio tail-off.

### Typography
- Narration text: Inter Medium, 36px, #FFFFFF (active) / rgba(255,255,255,0.4) (inactive)
- Voice badge: Inter Regular, 14px, #8EC8E8
- Word highlight transition: 3-frame crossfade per word

### Easing
- Word reveal: `easeOutQuad`
- Waveform bar oscillation: `easeInOutSine` (per bar, phase-shifted)
- Badge slide-in: `easeOutCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={155} durationInFrames={38}>
  <AbsoluteFill>
    <AnimatedGradientMesh colors={['#0A1628', '#1B3A5C', '#0D4D4D']} />
    <Sequence from={6}>
      <WaveformVisualizer
        bars={64}
        baseY={680}
        maxHeight={280}
        color="#4DA8DA"
      />
    </Sequence>
    <Sequence from={6}>
      <WordByWordReveal
        text="It uses Veo-generated clips with narration overlay."
        wordsPerBeat={1}
        framePadding={5}
      />
    </Sequence>
    <Sequence from={0}>
      <VoiceBadge label="TTS: Qwen3 — Aiden" />
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "narrationText": "It uses Veo-generated clips with narration overlay.",
  "voiceEngine": "Qwen3",
  "voiceSpeaker": "Aiden",
  "waveformBars": 64,
  "words": ["It", "uses", "Veo-generated", "clips", "with", "narration", "overlay."]
}
```
