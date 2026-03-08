[Remotion] Animated Subtitle Track — Word-by-Word Narration

# Section 0.3: Animated Subtitle Track

**Tool:** Remotion
**Duration:** ~15.68s (full section)
**Timestamp:** 0:00 - 0:15.68

## Visual Description
A word-by-word animated subtitle track positioned in the lower third of the screen. Words appear in sync with the narration audio, using a rolling 12-word window. Each new word pops in with a subtle scale animation while previous words remain visible. The active word is highlighted in bright white; trailing words dim to 60% opacity. A semi-transparent dark backdrop ensures readability over any Veo background footage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: transparent overlay
- Subtitle region: bottom 20% of frame (y: 864 to 1040)

### Chart/Visual Elements
- Backdrop bar: full width, height 176px, anchored to bottom
  - Fill: rgba(15, 23, 42, 0.75)
  - Blur: backdrop-filter blur(8px)
  - Top edge: 1px solid rgba(59, 130, 246, 0.15)
- Text container: centered horizontally, max-width 1600px, padding 24px 40px
- Word highlight: current word scaled to 1.05x with full white opacity
- Rolling window: displays up to 12 words at a time, oldest words fade out left

### Animation Sequence
1. **Each word arrival:** Scale 0.85→1.0 over 4 frames, opacity 0→1 over 4 frames
2. **Active word:** Full white (#FFFFFF), scale 1.05x
3. **Previous words:** Dim to rgba(255, 255, 255, 0.6), scale back to 1.0x over 3 frames
4. **Window overflow:** When >12 words visible, oldest word fades out (opacity 1→0 over 6 frames) and slides left 20px
5. **Segment gaps:** 0.3s silence between narration segments — subtitle holds last state, then clears with a 10-frame fade

### Typography
- Words: Inter Medium, 36px, white (#FFFFFF)
- Active word: Inter SemiBold, 36px, white (#FFFFFF)
- Word spacing: 12px
- Text shadow: 0 2px 8px rgba(0, 0, 0, 0.5)

### Easing
- Word pop-in: `easeOutBack` (slight overshoot for punch)
- Word dim: `easeOutQuad`
- Window slide: `easeInOutCubic`

## Narration Sync
> "If you use Cursor, Claude Code, or Copilot — you're getting really good at this. Your grandmother figured out socks got cheap, and she stopped darning. Code just got that cheap. So why are we still patching?"

Words are timed from `cold_open/word_timestamps.json`. Each word appears at its spoken timestamp.

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={470}>
  {/* Backdrop bar */}
  <SubtitleBackdrop />
  {/* Word-by-word renderer */}
  <WordByWordSubtitle
    words={wordTimestamps}
    windowSize={12}
    activeStyle={{ color: '#FFFFFF', fontWeight: 600, transform: 'scale(1.05)' }}
    trailStyle={{ color: 'rgba(255,255,255,0.6)', fontWeight: 500, transform: 'scale(1.0)' }}
    popInDuration={4}
    dimDuration={3}
  />
</Sequence>
```

## Data Points
```json
{
  "narration_segments": [
    "cold_open_001", "cold_open_002", "cold_open_003",
    "cold_open_004", "cold_open_005", "cold_open_006"
  ],
  "word_timestamps_source": "cold_open/word_timestamps.json",
  "window_size": 12,
  "silence_gap_seconds": 0.3,
  "total_duration_seconds": 15.68,
  "total_frames_at_30fps": 470
}
```

---
