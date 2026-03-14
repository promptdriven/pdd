[veo: An aerial drone shot of a green forest canopy with sunlight filtering through the leaves]

# Section 2.3: Aerial Forest Canopy

**Tool:** Veo (AI-generated video)
**Duration:** ~2.0s
**Timestamp:** 0:10 – 0:12

## Visual Description
An aerial drone shot looking down (or at a slight angle) onto a dense green forest canopy. Sunlight filters through the leaves, creating dappled light patterns and subtle lens flare. The camera drifts slowly forward, giving a sense of serene, cinematic movement over the treetops. Lush greens dominate the palette with warm highlights where sunlight penetrates the foliage. No text or data overlays — pure Veo-generated B-roll footage.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: N/A (full-bleed video)
- No grid lines

### Chart/Visual Elements
- **Primary subject:** Dense forest canopy viewed from above, filling the entire frame
- **Lighting:** Dappled sunlight — warm highlights (#E8D44D) piercing through deep greens (#1A5E1A to #2D7A2D)
- **Depth of field:** Moderate — nearest treetops in focus, distant canopy gently softened
- **Motion:** Slow forward drift (drone advancing at ~2m/s feel), slight parallax between tree layers
- **Atmosphere:** Faint volumetric haze where light beams cut through gaps in the canopy

### Animation Sequence
1. **Frame 0–12 (0–0.4s):** Clip crossfades from previous scene (opacity 0→1)
2. **Frame 12–50 (0.4–1.67s):** Continuous drone movement over canopy. Sunlight shafts shift subtly as perspective changes
3. **Frame 50–60 (1.67–2.0s):** Hold or gentle slow-down as clip prepares to hand off to next visual

### Typography
- None (pure footage)

### Easing
- Crossfade in: `easeInOutQuad`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={90} durationInFrames={60}>
  <VeoClip
    src="/veo/aerial_forest_canopy.mp4"
    fadeInFrames={12}
    playbackRate={1.0}
  />
</Sequence>
```

## Data Points
```json
{
  "veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "source_file": "aerial_forest_canopy.mp4",
  "aspect_ratio": "16:9",
  "style": "cinematic aerial drone",
  "color_temperature": "natural green with warm highlights"
}
```

---
