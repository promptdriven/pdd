[Remotion] Word-by-Word Narration Subtitle Track

# Section 2.10: Subtitle Track — Rolling Word-by-Word Narration

**Tool:** Remotion
**Duration:** ~195.79s (full Part 2)
**Timestamp:** 0:00 - 3:15

## Visual Description
A persistent subtitle overlay at the bottom third of the frame, displaying narration text word-by-word in sync with the audio. The subtitle uses a 12-word rolling window — as new words appear, oldest words scroll off the left. The current word highlights briefly as it's spoken. The text sits on a semi-transparent dark band that ensures readability over any background. The subtitle track runs across the entire Part 2 duration, appearing after the title card fades and persisting until the final fade-to-black.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Subtitle region: full width, y=880 to y=1000 (bottom ~11% of frame)
- Text center: y=940, horizontally centered

### Chart/Visual Elements
- Backdrop band: full-width rectangle from y=860 to y=1020
  - Color: rgba(0, 0, 0, 0.55)
  - Blur: backdrop-filter blur(4px)
  - Top/bottom edge: feathered gradient (20px), hard band → transparent
- Text container: max-width 1600px, centered horizontally
- Word display: 12-word rolling window
  - Current word: full white (#FFFFFF), slight scale 1.05x, bold weight
  - Recent words (spoken within last 0.5s): #FFFFFF at 90% opacity
  - Older words: #CBD5E1 at 70% opacity
  - Words scroll left as new words appear — smooth translateX animation

### Animation Sequence
1. **Frame 150 (after title card):** Subtitle track fades in — backdrop opacity 0→0.55 over 15 frames.
2. **Continuous:** Words appear one at a time, synced to `word_timestamps.json`.
3. **Per word:** New word appears at right of current window, pushes older words left. Current word highlights for ~200ms then dims.
4. **At segment boundaries:** Brief pause (0.3s silence gap), window may soft-reset.
5. **Frame 5844-5874 (final 30 frames):** Subtitle fades out with the overall fade-to-black.

### Word Timing
- Source: `part2_paradigm_shift/word_timestamps.json`
- Each entry: `{ "word": "string", "start": float_seconds, "end": float_seconds }`
- Words render at `start` time, highlight through `end` time
- Rolling window: last 12 words visible, oldest fade/scroll off
- Segments: `part2_paradigm_shift_001` through `part2_paradigm_shift_019`
- Default silence gap: 0.3s between segments

### Typography
- Words: Inter Medium, 36px
  - Current: #FFFFFF, font-weight 700, scale 1.05
  - Recent: #FFFFFF at 90% opacity, font-weight 500
  - Older: #CBD5E1 at 70% opacity, font-weight 400
- Letter spacing: 0.01em
- Word spacing: 10px
- Text shadow: 0 2px 8px rgba(0, 0, 0, 0.8)

### Easing
- Word appear: `easeOutQuad` (opacity 0→1, 6 frames)
- Word highlight scale: `easeOutCubic` then `easeInCubic`
- Window scroll: `easeInOutQuad` (smooth lateral shift)
- Track fade in/out: `easeInOutCubic`

## Narration Sync
> Synced to every word in the Part 2 narration via word_timestamps.json

Full narration text (19 segments):
> "Not cheaper materials — a shift in how things are made. The same pattern across textiles, plastics, semiconductors. The value didn't stay in the thing itself. Design the mold once, produce unlimited identical parts. Find a defect? Fix the mold — not every individual part. The cost is in the specification, not the production. Value migrates from the object to the specification. The plastic part is disposable. The mold is everything. 1980s — engineers hand-drew gate layouts. 1985 — Verilog HDL: describe behavior, not wires. Synopsys added verification with SAT and SMT solvers. Same revolution: specification replaced manual construction. The prompt is your mold. Code is plastic. Tests lock the behavior. We've seen this before — we just didn't recognize it."

This component reads the full word timestamps file and renders each word at its precise timing, maintaining a sliding window of visible text.

## Code Structure (Remotion)
```typescript
<Sequence from={SUBTITLE_START} durationInFrames={PART2_TOTAL_FRAMES}>
  <AbsoluteFill style={{ pointerEvents: 'none' }}>
    {/* Backdrop band */}
    <SubtitleBackdrop
      opacity={interpolate(frame, [0, 15, PART2_TOTAL_FRAMES - 30, PART2_TOTAL_FRAMES], [0, 0.55, 0.55, 0])}
    />

    {/* Rolling word display */}
    <SubtitleWords
      words={wordTimestamps}
      currentFrame={frame}
      fps={30}
      windowSize={12}
      renderWord={(word, state) => (
        <span style={{
          color: state === 'current' ? '#FFFFFF' : state === 'recent' ? 'rgba(255,255,255,0.9)' : '#CBD5E1',
          fontWeight: state === 'current' ? 700 : state === 'recent' ? 500 : 400,
          transform: state === 'current' ? 'scale(1.05)' : 'scale(1)',
          opacity: state === 'fading' ? 0.4 : 1,
          transition: 'all 0.15s ease',
        }}>
          {word.text}{' '}
        </span>
      )}
    />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "word_timestamps_file": "part2_paradigm_shift/word_timestamps.json",
  "narration_audio": "part2_paradigm_shift/narration.wav",
  "segment_count": 19,
  "segment_prefix": "part2_paradigm_shift",
  "silence_gap_seconds": 0.3,
  "window_size": 12,
  "subtitle_region": {"y_start": 860, "y_end": 1020, "text_y": 940},
  "backdrop_opacity": 0.55,
  "typography": {
    "font": "Inter",
    "base_size": 36,
    "current_weight": 700,
    "default_weight": 400
  },
  "total_duration_seconds": 195.79,
  "fps": 30
}
```

---
