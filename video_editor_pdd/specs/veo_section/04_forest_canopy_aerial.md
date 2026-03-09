[veo:]

# Section 2.4: Forest Canopy Aerial

**Tool:** Veo (AI-generated footage)
**Duration:** ~3s
**Timestamp:** 0:09 - 0:12

## Visual Description
An aerial drone shot looking down over a lush green forest canopy with sunlight filtering through the leaves. The camera drifts slowly forward, creating a sense of peaceful exploration. Shafts of golden light pierce through gaps in the foliage, creating dappled patterns on the lower canopy layers. No text overlays — pure cinematic nature B-roll.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: N/A (full-frame video footage)

### Chart/Visual Elements
- Full-frame Veo-generated video clip
- Color palette: Deep emerald (#065F46), forest green (#166534), golden light (#FBBF24), shadow (#1A2E05)
- Camera angle: Top-down aerial, slight forward drift
- Motion: Slow forward dolly, ~0.5m/s apparent speed

### Animation Sequence
1. **Frame 0-90 (0-3s):** Continuous aerial footage plays. Camera drifts forward over canopy. Sunlight shafts shift subtly as perspective changes. No additional Remotion overlays.

### Typography
- None — pure footage

### Easing
- N/A (video playback)

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={270} durationInFrames={90}>
  <OffthreadVideo
    src={staticFile("veo/forest_canopy_aerial.mp4")}
    style={{ width: "100%", height: "100%", objectFit: "cover" }}
  />
</Sequence>
```

## Data Points
```json
{
  "veoPrompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "clipSource": "veo/forest_canopy_aerial.mp4",
  "playbackRate": 1.0
}
```

---
