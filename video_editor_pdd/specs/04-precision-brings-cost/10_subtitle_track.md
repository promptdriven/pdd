[Remotion] Word-by-Word Narration Subtitle Track

# Section 4.9: Subtitle Track — Rolling Word-by-Word Narration

**Tool:** Remotion
**Duration:** ~96.91s (full Part 4 duration)
**Timestamp:** 0:00 - 1:36

## Visual Description
A persistent subtitle overlay that runs across the entire Part 4 composition. Words appear one at a time in sync with the narration audio, using a 12-word rolling window. The current word is highlighted in white while surrounding words are semi-transparent. The subtitle block sits at the bottom third of the frame on a semi-transparent black backdrop bar. As new words arrive, older words scroll left and fade out. The effect creates a karaoke-style reading experience that keeps viewers anchored to the narration even when complex visuals dominate the upper portion of the frame.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay (top-most layer)
- Subtitle region: full width, y=880 to y=1040 (160px tall)
- Backdrop bar: full width, y=870 to y=1050, rgba(0, 0, 0, 0.6) with 8px feathered edges

### Chart/Visual Elements
- Backdrop bar: rgba(0, 0, 0, 0.6), full width, 180px tall, centered at y=960
- Feathered edges: top and bottom 8px gradient to transparent
- Word display: 12-word rolling window, centered horizontally
- Current word: #FFFFFF at 100% opacity, slight scale bump (1.05x)
- Previous words (in window): #FFFFFF at 50% opacity
- Next words (in window): #FFFFFF at 30% opacity
- Word spacing: proportional, ~12px between words
- Line wrapping: single line, no wrap — window scrolls horizontally

### Animation Sequence
1. **Frame 0-15 (0-0.5s):** Backdrop bar fades in — opacity 0→0.6.
2. **Per-word timing:** Each word highlight syncs to `word_timestamps.json` entries.
   - Current word: opacity jumps to 1.0, scale 1.0→1.05 over 3 frames, then 1.05→1.0 over 6 frames.
   - Previous word: opacity drops from 1.0→0.5 over 6 frames.
   - Window scroll: when current word would exceed right edge of 12-word window, oldest word slides left and fades out (opacity 0.5→0 over 10 frames), new word slides in from right (opacity 0→0.3).
3. **Frame (end-15) to end:** Backdrop bar fades out — opacity 0.6→0.

### Typography
- Words: Inter SemiBold, 36px, #FFFFFF (variable opacity)
- Current word underline: 2px, #F59E0B at 60% opacity (amber accent matching Part 4 theme)
- Letter-spacing: -0.01em
- Text shadow: 0 2px 8px rgba(0, 0, 0, 0.8)

### Easing
- Word highlight scale: `easeOutQuad`
- Word fade: `easeOutQuad`
- Window scroll: `easeInOutCubic`
- Backdrop fade: `easeInOutCubic`

## Narration Sync
> Full narration text for Part 4:
> "Precision has a cost. More detailed prompts mean slower generation. More comprehensive tests mean longer feedback cycles. This is the trade-off. There's a sweet spot between vagueness and over-specification. Too little precision — AI hallucinates. Too much — you're writing the code yourself. The U-curve has a minimum. Adjust precision based on context. Greenfield project? Lighter prompts, explore fast. Legacy system with strict contracts? Heavy test walls, precise prompts. The spectrum is a tool, not a rule."

Word timestamps are loaded from `part4_precision/word_timestamps.json`. Each entry contains `{ "word": string, "start": float, "end": float }`.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={TOTAL_FRAMES}>
  {/* Backdrop bar */}
  <AbsoluteFill style={{
    top: 870,
    height: 180,
    background: `linear-gradient(
      to bottom,
      transparent,
      rgba(0,0,0,0.6) 8px,
      rgba(0,0,0,0.6) calc(100% - 8px),
      transparent
    )`,
    opacity: interpolate(frame, [0, 15, TOTAL_FRAMES - 15, TOTAL_FRAMES], [0, 1, 1, 0]),
  }} />

  {/* Rolling word display */}
  <SubtitleTrack
    words={wordTimestamps}
    windowSize={12}
    fps={30}
    currentFrame={frame}
    style={{
      position: 'absolute',
      top: 890,
      width: '100%',
      textAlign: 'center',
    }}
    activeStyle={{ opacity: 1, transform: 'scale(1.05)', color: '#FFFFFF' }}
    inactiveStyle={{ opacity: 0.5, color: '#FFFFFF' }}
    upcomingStyle={{ opacity: 0.3, color: '#FFFFFF' }}
    underlineColor="#F59E0B"
  />
</Sequence>
```

## Data Points
```json
{
  "narration_source": "part4_precision/narration.wav",
  "timestamps_source": "part4_precision/word_timestamps.json",
  "window_size": 12,
  "total_duration_seconds": 96.91,
  "total_frames_at_30fps": 2907,
  "backdrop_color": "rgba(0, 0, 0, 0.6)",
  "accent_color": "#F59E0B",
  "font_size": 36,
  "fps": 30
}
```

---
