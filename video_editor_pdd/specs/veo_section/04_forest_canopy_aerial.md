[veo:]

# Section 2.4: Forest Canopy Aerial

**Tool:** Veo
**Duration:** ~3s
**Timestamp:** 0:05 - 0:08

## Visual Description
An aerial drone shot looking straight down at a lush green forest canopy. Sunlight filters through gaps in the leaves, creating dappled pools of golden light on the canopy surface. The camera drifts slowly forward, revealing the organic fractal patterns of treetops. The color palette is rich emerald greens with warm golden highlights where the sun penetrates. Slight atmospheric haze adds depth between the canopy layers.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: n/a (full-frame video)
- Grid lines: none

### Chart/Visual Elements
- Full-frame Veo-generated video clip
- No overlay graphics during this beat
- Color grading: lush naturalistic (boosted greens in midtones, warm golden highlights)
- Speed: 1.0x real-time
- Camera: slow forward drift (~2px/frame equivalent movement)

### Animation Sequence
1. **Frame 0-90 (0-3s):** Continuous aerial footage. Camera drifts slowly forward over canopy. Sunlight beams shift subtly as perspective changes.

### Typography
- None (pure video footage)

### Easing
- Clip fade-in: `easeOutQuad` (0.3s crossfade from previous visual)
- Clip fade-out: `easeInQuad` (0.3s crossfade to next visual)

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Veo Prompt
```
An aerial drone shot of a green forest canopy with sunlight filtering through the leaves
```

## Code Structure (Remotion)
```typescript
<Sequence from={150} durationInFrames={90}>
  <AbsoluteFill>
    <OffthreadVideo
      src={staticFile("veo_section/forest_canopy_aerial.mp4")}
      playbackRate={1.0}
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
  "veoPrompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "playbackRate": 1.0,
  "crossfadeDuration": 9,
  "clipSource": "veo_section/forest_canopy_aerial.mp4"
}
```

---
