[veo: A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion]

# Section 2.2: Ocean Wave Sunset

**Tool:** Veo (AI-generated video)
**Duration:** ~2.0s
**Timestamp:** 0:08 – 0:10

## Visual Description
A cinematic slow-motion clip of a calm ocean wave rolling onto a sandy beach at sunset. Golden-hour light reflects off the water surface, casting warm amber and soft orange tones across the scene. The camera holds a low-angle or aerial drone perspective, emphasizing the gentle curvature of the wave crest as it breaks onto wet sand. No text or data overlays — this is pure Veo-generated B-roll footage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: N/A (full-bleed video)
- No grid lines

### Chart/Visual Elements
- **Primary subject:** Single ocean wave rolling shoreward, filling the frame
- **Lighting:** Golden hour — warm tones (#FFB347 to #FF6B35 gradient in the sky, soft gold (#C9A84C) reflections on water)
- **Depth of field:** Shallow — wave crest in sharp focus, distant horizon softly blurred
- **Motion:** Slow-motion (0.5x playback feel), wave advancing left-to-right across the frame

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Clip fades in from black (opacity 0→1) as the wave begins to crest
2. **Frame 15–50 (0.5–1.67s):** Wave rolls forward, foam spreads across the sand. Camera holds steady or tracks gently
3. **Frame 50–60 (1.67–2.0s):** Hold on the receding water with golden reflections — natural endpoint

### Typography
- None (pure footage)

### Easing
- Fade in: `easeOutQuad`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={30} durationInFrames={60}>
  <VeoClip
    src="/veo/ocean_wave_sunset.mp4"
    fadeInFrames={15}
    playbackRate={1.0}
  />
</Sequence>
```

## Data Points
```json
{
  "veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "source_file": "ocean_wave_sunset.mp4",
  "aspect_ratio": "16:9",
  "style": "cinematic slow motion",
  "color_temperature": "warm golden hour"
}
```

---
