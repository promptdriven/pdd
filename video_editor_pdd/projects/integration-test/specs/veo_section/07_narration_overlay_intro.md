[Remotion]

# Section 2.7: Narration Overlay Intro

**Tool:** Remotion
**Duration:** ~2.5s
**Timestamp:** 0:13.5 – 0:16

## Visual Description
A lower-third narration overlay composited on the Veo footage. A frosted-glass panel rises from the bottom of the frame, containing a word-by-word caption that highlights each word in sync with the narration audio. A waveform visualizer (5 vertical bars) pulses alongside the text, indicating active narration. A gold accent underline draws beneath the caption text. The overall effect is a polished broadcast-style lower third.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: Transparent overlay (composited on Veo footage beneath)
- No grid lines

### Chart/Visual Elements
- **Frosted Panel:** Blurred background rect, 1920×200px, anchored at bottom of frame
  - Background: `rgba(11,17,32,0.75)` with `backdrop-filter: blur(20px)`
  - Top border: 1px `rgba(201,168,76,0.4)`
- **Caption Text:** "It uses Veo-generated clips with narration overlay."
  - Displayed as individual words, each highlighting gold when active
  - Inactive words: `rgba(255,255,255,0.5)`
  - Active word: `#C9A84C` (gold) with slight scale-up to 1.05
- **Waveform Visualizer:** 5 vertical bars, positioned left of caption text
  - Bar width: 4px, spacing: 6px
  - Color: `#C9A84C` (gold)
  - Height oscillates between 8px and 40px based on audio energy
  - Position: x=80, y=center of panel
- **Gold Accent Underline:** Horizontal line beneath caption text
  - Color: `#C9A84C`, 2px thick
  - Draws from left to right, width matching text block

### Animation Sequence
1. **Frame 0–10 (0–0.33s):** Frosted panel slides up from below frame to final position. Waveform bars begin oscillating.
2. **Frame 10–17 (0.33–0.57s):** Word "It" highlights gold.
3. **Frame 17–24 (0.57–0.8s):** Word "uses" highlights; "It" dims back.
4. **Frame 24–31 (0.8–1.03s):** Word "Veo-generated" highlights.
5. **Frame 31–38 (1.03–1.27s):** Word "clips" highlights.
6. **Frame 38–45 (1.27–1.5s):** Word "with" highlights.
7. **Frame 45–52 (1.5–1.73s):** Word "narration" highlights.
8. **Frame 52–60 (1.73–2.0s):** Word "overlay." highlights. Gold underline finishes drawing.
9. **Frame 60–75 (2.0–2.5s):** All words turn gold briefly, then panel slides down and fades out.

### Typography
- Caption words: Inter Medium, 36px
  - Inactive: `rgba(255,255,255,0.5)`
  - Active: `#C9A84C`, scale 1.05
- Lower-third label (optional): Inter Regular, 14px, `rgba(255,255,255,0.4)`

### Easing
- Panel slide-up: `easeOutCubic`
- Word highlight: `easeOutQuad` (color + scale transition)
- Underline draw: `linear`
- Waveform bars: `easeInOutSine` (oscillation)
- Panel slide-down: `easeInCubic`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

Word-level timing (frame numbers at 30fps):
| Word | Frame |
|------|-------|
| It | 10 |
| uses | 17 |
| Veo-generated | 24 |
| clips | 31 |
| with | 38 |
| narration | 45 |
| overlay. | 52 |

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={75}>
  <BlurredBackground />
  <FrostedPanel height={200}>
    <WaveformVisualizer bars={5} />
    <Sequence from={0}>
      <WordByWordText
        words={['It','uses','Veo-generated','clips','with','narration','overlay.']}
        timings={[10, 17, 24, 31, 38, 45, 52]}
        activeColor="#C9A84C"
        inactiveColor="rgba(255,255,255,0.5)"
      />
    </Sequence>
    <Sequence from={10}>
      <GoldAccentLine />
    </Sequence>
  </FrostedPanel>
</Sequence>
```

## Data Points
```json
{
  "caption": "It uses Veo-generated clips with narration overlay.",
  "words": ["It", "uses", "Veo-generated", "clips", "with", "narration", "overlay."],
  "word_timings_frames": [10, 17, 24, 31, 38, 45, 52],
  "waveform_bars": 5,
  "panel_height": 200,
  "active_color": "#C9A84C",
  "inactive_color": "rgba(255,255,255,0.5)"
}
```

---
