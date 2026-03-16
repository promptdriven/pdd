[Remotion]

# Section 0.5: "So Why Are We Still Patching?"

**Tool:** Remotion
**Duration:** ~2s (60 frames @ 30fps)
**Timestamp:** 0:16 - 0:18

## Visual Description

The clean regenerated code from 04 is still on screen. The question lands over the code as a single line of bold white text, centered vertically. The text fades in word by word, timed to the narration. Each word appears with a slight upward motion (8px).

The code behind dims to 20% opacity as the text appears, creating depth separation. A subtle spotlight effect — a soft radial gradient — focuses behind the text. This is the rhetorical question that anchors the entire video's thesis.

After the full question is visible, a brief beat of stillness. The viewer sits with the question.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: #1E1E2E (editor, carried from 04) dimmed to 20% opacity over #0A0F1A
- Spotlight: radial gradient from rgba(74,144,217,0.08) centered at (960, 540), radius 400px

### Chart/Visual Elements

**Background Code**
- Carried from 04 (clean function), opacity animates 1.0 → 0.2

**Spotlight**
- Radial gradient: rgba(74,144,217,0.08) → transparent
- Center: (960, 540)
- Radius: 400px

**Question Text**
- "So why are we still patching?"
- Six words, each appearing sequentially
- Position: centered at (960, 540)
- Word spacing timed to narration word timestamps

### Animation Sequence
1. **Frame 0-10 (0-0.33s):** Code from 04 dims from 100% to 20% opacity. Spotlight fades in.
2. **Frame 10-18 (0.33-0.6s):** "So" appears — fade in + 8px upward motion.
3. **Frame 18-22 (0.6-0.73s):** "why" appears.
4. **Frame 22-28 (0.73-0.93s):** "are" appears.
5. **Frame 28-32 (0.93-1.07s):** "we" appears.
6. **Frame 32-38 (1.07-1.27s):** "still" appears.
7. **Frame 38-48 (1.27-1.6s):** "patching?" appears — slightly slower fade, landing with emphasis.
8. **Frame 48-60 (1.6-2.0s):** Hold. All words visible. Stillness.

### Typography
- Question text: `Inter`, 52px, weight 600, #FFFFFF, opacity 0.95
- Letter spacing: 0.5px
- Line height: 1.2

### Easing
- Code dim: `easeOut(quad)`
- Spotlight fade: `easeOut(quad)`
- Word fade-in: `easeOut(cubic)` on opacity, `easeOut(quad)` on y-position
- Final word ("patching?"): `easeOut(cubic)` with 1.5× duration

## Narration Sync
> "So why are we still patching?"

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={60}>
  <Sequence from={0} durationInFrames={10}>
    <FadeOpacity from={1.0} to={0.2}>
      <CleanFunction lines={14} />
    </FadeOpacity>
  </Sequence>
  <SpotlightGradient center={[960, 540]} radius={400} color="rgba(74,144,217,0.08)" />
  <WordByWordReveal
    text="So why are we still patching?"
    startFrame={10}
    position={[960, 540]}
    font={{ family: "Inter", size: 52, weight: 600, color: "#FFFFFF" }}
    wordTimings={[
      { word: "So", frame: 10, duration: 8 },
      { word: "why", frame: 18, duration: 4 },
      { word: "are", frame: 22, duration: 6 },
      { word: "we", frame: 28, duration: 4 },
      { word: "still", frame: 32, duration: 6 },
      { word: "patching?", frame: 38, duration: 10 }
    ]}
    motionY={8}
  />
</Sequence>
```

## Data Points
```json
{
  "background": {
    "codeOpacityStart": 1.0,
    "codeOpacityEnd": 0.2,
    "baseColor": "#0A0F1A"
  },
  "spotlight": {
    "color": "rgba(74,144,217,0.08)",
    "center": [960, 540],
    "radius": 400
  },
  "text": {
    "fullText": "So why are we still patching?",
    "font": "Inter",
    "fontSize": 52,
    "fontWeight": 600,
    "color": "#FFFFFF",
    "opacity": 0.95,
    "position": [960, 540],
    "letterSpacing": 0.5,
    "motionY": 8
  },
  "wordTimings": [
    { "word": "So", "startFrame": 10, "durationFrames": 8 },
    { "word": "why", "startFrame": 18, "durationFrames": 4 },
    { "word": "are", "startFrame": 22, "durationFrames": 6 },
    { "word": "we", "startFrame": 28, "durationFrames": 4 },
    { "word": "still", "startFrame": 32, "durationFrames": 6 },
    { "word": "patching?", "startFrame": 38, "durationFrames": 10 }
  ],
  "narrationSegments": ["cold_open_006"],
  "narrationTimingSeconds": { "start": 16.02, "end": 17.54 }
}
```

---
