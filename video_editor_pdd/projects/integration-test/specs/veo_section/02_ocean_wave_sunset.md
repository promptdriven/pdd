[veo:]

# Section 2.2: Ocean Wave Sunset B-Roll

**Tool:** Veo 3.1
**Duration:** ~4s
**Timestamp:** 0:10 – 0:14

## Visual Description
Cinematic slow-motion footage of a calm ocean wave rolling onto a sandy beach at sunset. Golden-hour light catches the crest of the wave as it curls and breaks gently onto wet sand. The camera is low-angle, near the waterline, creating an immersive perspective. Warm amber and deep blue tones dominate the palette. No text overlay — pure footage.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: N/A (full-bleed video)
- No grid lines

### Chart/Visual Elements
- **Source Clip:** `veo/04_veo_broll.mp4`
- **Veo Prompt:** "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion"
- **Color Grade:** Warm sunset tones — amber highlights, teal shadows
- **Motion:** Slow-motion wave roll, gentle camera drift

### Animation Sequence
1. **Frame 0–15 (0–0.5s):** Clip fades in from previous composition. Wave approaching shore.
2. **Frame 15–90 (0.5–3.0s):** Main footage — wave crests, curls, and washes onto sand. Slow-motion movement.
3. **Frame 90–120 (3.0–4.0s):** Wave recedes. Clip continues playing to natural end point.

### Typography
- None — pure cinematic footage

### Easing
- Fade-in: `linear` (handled by Remotion Sequence transition)

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <OffthreadVideo
    src={staticFile('veo_section/veo/04_veo_broll.mp4')}
    style={{ width: '100%', height: '100%', objectFit: 'cover' }}
  />
</Sequence>
```

## Data Points
```json
{
  "source": "veo/04_veo_broll.mp4",
  "veo_prompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "duration_seconds": 4.0,
  "veo_model": "veo-3.1-generate-001"
}
```

---
