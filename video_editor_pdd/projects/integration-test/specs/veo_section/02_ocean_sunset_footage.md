[veo: A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion]

# Section 2.2: Ocean Sunset Footage

**Tool:** Veo
**Duration:** ~5s
**Timestamp:** 0:03 - 0:08

## Visual Description
A cinematic slow-motion clip of a calm ocean wave rolling onto a sandy beach at sunset. The camera is positioned low, just above the waterline, capturing the golden-hour light reflecting off the wave surface. Warm amber and soft pink tones fill the sky. The wave curls gently, spreads across the wet sand, and recedes. No text overlays — this is pure B-roll footage with narration audio layered on top.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: N/A (full-frame video footage)

### Visual Elements
- **Subject:** Single ocean wave, medium height, rolling toward camera
- **Lighting:** Golden hour — warm amber sun low on the horizon, soft pink/orange sky gradient
- **Camera:** Low-angle, nearly at water level, steady or very slight dolly backward
- **Motion:** Slow motion (approx 60fps interpreted at 30fps for half-speed feel)
- **Color palette:** Warm golds (#D4A843), soft corals (#E8967A), deep ocean blue (#1B4F72), wet sand (#C4A35A)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Wave approaches from mid-distance, light catches the crest
2. **Frame 30-90 (1-3s):** Wave curls and breaks gently, foam spreads across sand
3. **Frame 90-150 (3-5s):** Water spreads thin across beach, recedes; sky holds warm glow

### Typography
- No on-screen text

### Easing
- N/A (live footage, no programmatic easing)

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={90} durationInFrames={150}>
  <Video src={veoClip("ocean_sunset")} />
  <Audio src={narration("veo_section_001")} />
</Sequence>
```

## Data Points
```json
{
  "veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "clip_id": "ocean_sunset",
  "audio_segment": "veo_section_001"
}
```

---
