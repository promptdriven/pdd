[veo:]

# Section 2.2: Ocean Sunset B-Roll

**Tool:** Veo (AI-Generated Video)
**Duration:** ~1.3s
**Timestamp:** 0:01 - 0:03

## Visual Description
Full-screen cinematic Veo-generated footage of a calm ocean wave rolling onto a sandy beach at sunset. Golden hour light reflects off the water surface. The shot is slow-motion, captured from a low-angle perspective near the waterline. Warm amber and deep blue tones dominate. This clip plays behind a subtle lower-third narration badge. The footage has a dreamy, contemplative quality with gentle wave motion.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Veo-generated video fills entire frame
- No grid lines

### Chart/Visual Elements
- **Veo video layer:** Full-bleed `<OffthreadVideo>` component, objectFit cover, z-index 0
- **Color grade overlay:** Linear gradient from transparent (top 60%) to rgba(10, 22, 40, 0.6) at bottom, z-index 1
- **Lower-third narration badge:** Semi-transparent dark bar (rgba(0,0,0,0.5)) at y=880, height 80px, full width, z-index 2
- **Narration text:** Displayed inside the lower-third bar, left-padded 80px

### Animation Sequence
1. **Frame 0-8 (0-0.27s):** Veo clip fades in from black (opacity 0 → 1). Lower-third bar slides up from bottom (translateY 80 → 0).
2. **Frame 8-30 (0.27-1.0s):** Video plays at normal speed. Narration text holds visible.
3. **Frame 30-38 (1.0-1.27s):** Gentle crossfade begins toward next visual (opacity 1.0 → 0.7).

### Typography
- Narration text: Inter Medium, 20px, #FFFFFF, opacity 0.9

### Easing
- Video fade-in: `easeOutQuad`
- Lower-third slide: `easeOutCubic`
- Crossfade out: `linear`

## Narration Sync
> "This is the second section of the integration test video."

## Code Structure (Remotion)
```typescript
<Sequence from={38} durationInFrames={38}>
  <AbsoluteFill>
    <OffthreadVideo
      src={staticFile("veo/04_veo_broll.mp4")}
      style={{ width: '100%', height: '100%', objectFit: 'cover' }}
    />
    <GradientOverlay direction="bottom" opacity={0.6} />
    <Sequence from={0}>
      <LowerThirdBadge>
        <NarrationText text="This is the second section of the integration test video." />
      </LowerThirdBadge>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "veoPrompt": "A calm ocean wave rolling onto a sandy beach at sunset, cinematic, slow motion",
  "videoFile": "veo/04_veo_broll.mp4",
  "narration": "This is the second section of the integration test video.",
  "audioFile": "tts/veo_section_001.wav"
}
```
