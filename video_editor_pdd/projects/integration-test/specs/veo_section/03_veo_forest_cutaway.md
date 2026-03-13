[veo:]

# Section 2.3: Aerial Forest Cutaway

**Tool:** Veo (AI-Generated Video)
**Duration:** ~1.3s
**Timestamp:** 0:03 - 0:04

## Visual Description
Full-screen Veo-generated aerial drone footage looking down on a lush green forest canopy. Sunlight filters through gaps in the leaves, creating dappled light patterns and lens flares. The camera drifts slowly forward over the treetops. Rich emerald greens contrast with warm golden light shafts. This serves as a visual counterpoint to the ocean footage, demonstrating the range of Veo's cinematic generation capabilities.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: Veo-generated video fills entire frame
- No grid lines

### Chart/Visual Elements
- **Veo video layer:** Full-bleed `<OffthreadVideo>` component, objectFit cover, z-index 0
- **Light bloom overlay:** Radial gradient at top-right (rgba(255,220,150,0.15)), simulating sun position, z-index 1
- **Lower-third narration badge:** Same style as 02 — semi-transparent bar at y=880, z-index 2

### Animation Sequence
1. **Frame 0-6 (0-0.2s):** Crossfade in from previous ocean clip (opacity 0.3 → 1.0).
2. **Frame 6-32 (0.2-1.07s):** Video plays full. Light bloom overlay pulses gently (opacity 0.1 → 0.2 → 0.1).
3. **Frame 32-38 (1.07-1.27s):** Begin crossfade to next visual (opacity 1.0 → 0.8).

### Typography
- Narration text: Inter Medium, 20px, #FFFFFF, opacity 0.9

### Easing
- Crossfade in: `easeInOutQuad`
- Light bloom pulse: `easeInOutSine`
- Crossfade out: `linear`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={76} durationInFrames={38}>
  <AbsoluteFill>
    <OffthreadVideo
      src={staticFile("veo/05_veo_cutaway.mp4")}
      style={{ width: '100%', height: '100%', objectFit: 'cover' }}
    />
    <LightBloomOverlay position="top-right" opacity={0.15} />
    <Sequence from={0}>
      <LowerThirdBadge>
        <NarrationText text="It uses Veo-generated clips with narration overlay." />
      </LowerThirdBadge>
    </Sequence>
  </AbsoluteFill>
</Sequence>
```

## Data Points
```json
{
  "veoPrompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "videoFile": "veo/05_veo_cutaway.mp4",
  "narration": "It uses Veo-generated clips with narration overlay.",
  "audioFile": "tts/veo_section_002.wav"
}
```
