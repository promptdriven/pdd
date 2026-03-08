[veo:]

# Section 2.2: Ocean Wave at Sunset

**Tool:** Veo
**Duration:** ~3s
**Timestamp:** 0:02 - 0:05

## Visual Description
A cinematic slow-motion shot of a calm ocean wave rolling onto a sandy beach at sunset. Golden hour light bathes the scene in warm amber and peach tones. The wave curls gently, foam catching the light as it spreads across wet sand. The horizon glows with a gradient from deep orange to soft lavender. The camera is positioned low, nearly at water level, creating an immersive perspective.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: n/a (full-frame video)
- Grid lines: none

### Chart/Visual Elements
- Full-frame Veo-generated video clip
- No overlay graphics during this beat
- Color grading: warm cinematic (slight orange push in highlights, teal in shadows)
- Speed: 0.6x slow motion

### Animation Sequence
1. **Frame 0-90 (0-3s):** Continuous slow-motion footage. Wave approaches shore, crests, and rolls onto sand. Camera holds steady with subtle drift.

### Typography
- None (pure video footage)

### Easing
- Clip fade-in: `easeOutQuad` (0.3s crossfade from previous title card)
- Clip fade-out: `easeInQuad` (0.3s crossfade to next visual)

## Narration Sync
> "This is the second section of the integration test video."

## Veo Prompt
```
A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion
```

## Code Structure (Remotion)
```typescript
<Sequence from={60} durationInFrames={90}>
  <AbsoluteFill>
    <OffthreadVideo
      src={staticFile("veo_section/ocean_wave_sunset.mp4")}
      playbackRate={0.6}
      style={{ width: "100%", height: "100%", objectFit: "cover" }}
    />
    <CrossFade durationInFrames={9} direction="in" />
    <CrossFade durationInFrames={9} direction="out" />
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "veoPrompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "playbackRate": 0.6,
  "crossfadeDuration": 9,
  "clipSource": "veo_section/ocean_wave_sunset.mp4"
}
```

---
