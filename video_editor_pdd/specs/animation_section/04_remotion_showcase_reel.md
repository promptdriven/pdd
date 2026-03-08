[veo:]

# Section 1.4: Remotion Showcase — Developer B-Roll

**Tool:** Veo (AI-generated cinematic footage)
**Duration:** ~2s (60 frames)
**Timestamp:** 0:03 - 0:05

## Visual Description
Cinematic B-roll footage of a software developer's workspace. A close-up shot of a widescreen monitor displaying colorful animated charts and motion graphics in a code editor / preview environment. Shallow depth of field keeps the screen sharp while the background (keyboard, desk lamp, coffee mug) softly blurs. Warm ambient lighting with cool blue monitor glow reflected on the desk surface. Subtle camera dolly slides left-to-right across the scene.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Output format: MP4 (Veo-generated clip)

### Visual Elements
- **Primary subject:** Widescreen monitor showing animated data visualizations (bar charts, line graphs in motion)
- **Foreground:** Mechanical keyboard, partially visible, slightly out of focus
- **Background:** Minimalist desk setup — desk lamp with warm bulb, ceramic mug, small plant
- **Lighting:** Warm key light from upper-left (desk lamp), cool fill from monitor, dark ambient
- **Color palette:** Deep shadows (#0F172A), warm highlights (#F59E0B), cool monitor glow (#3B82F6)
- **Camera:** Slight left-to-right dolly, ~20px total travel over duration
- **Depth of field:** f/2.0 equivalent — monitor sharp, everything else falls off

### Veo Prompt
```
Cinematic close-up of a developer's widescreen monitor displaying colorful animated bar charts and motion graphics. Shallow depth of field, mechanical keyboard blurred in foreground. Warm desk lamp lighting, cool blue monitor glow reflecting on dark desk surface. Slow dolly movement left to right. 4K, photorealistic, moody studio lighting.
```

### Animation Sequence
1. **Frame 0-60 (0-2.0s):** Continuous slow dolly left-to-right, monitor content shows animated graphics in motion

### Typography
- None (pure B-roll footage)

### Easing
- Camera dolly: `linear` (constant speed pan)

## Narration Sync
> "It uses only Remotion animations with no Veo clips."

This B-roll plays during segment 2 (3.0s-5.0s). Ironically, this Veo clip contextualizes the Remotion animation pipeline being discussed — showing the developer environment where such animations are built.

## Code Structure (Remotion)
```typescript
<Sequence from={90} durationInFrames={60}>
  <Video src={staticFile('animation_section/04_remotion_showcase.mp4')} />
</Sequence>
```

## Data Points
```json
{
  "veoPrompt": "Cinematic close-up of a developer's widescreen monitor displaying colorful animated bar charts and motion graphics. Shallow depth of field, mechanical keyboard blurred in foreground. Warm desk lamp lighting, cool blue monitor glow reflecting on dark desk surface. Slow dolly movement left to right. 4K, photorealistic, moody studio lighting.",
  "duration": 2.0,
  "cameraMovement": "dolly-left-to-right",
  "depthOfField": "shallow"
}
```

---
