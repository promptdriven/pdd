[veo: An aerial drone shot of a green forest canopy with sunlight filtering through the leaves]

# Section 2.4: Aerial Forest Footage

**Tool:** Veo
**Duration:** ~5s
**Timestamp:** 0:12 - 0:17

## Visual Description
An aerial drone shot looking straight down at a lush green forest canopy. Sunlight filters through gaps in the leaves, creating dappled golden spots on the foliage below. The camera drifts slowly forward, revealing the texture and depth of the treetops. The footage has a warm, appreciative tone — natural greens with golden-hour warmth. No text overlays; narration audio plays over the clip.

## Technical Specifications

### Canvas
- Resolution: 1920x1080 (16:9)
- Background: N/A (full-frame video footage)

### Visual Elements
- **Subject:** Dense forest canopy seen from above (bird's-eye / top-down angle)
- **Lighting:** Late-afternoon sun — warm golden rays filtering through leaf gaps, creating light shafts and dappled patterns on lower foliage
- **Camera:** Aerial drone, top-down with slight forward drift (approx 2m/s equivalent)
- **Depth:** Multiple canopy layers visible — uppermost leaves in sharp focus, lower layers slightly softer
- **Color palette:** Forest green (#2D6A4F), emerald (#40916C), golden sunlight (#DAA520), dark shadow (#1B4332)

### Animation Sequence
1. **Frame 0-30 (0-1s):** Camera begins over dense canopy center, sunlight patches visible
2. **Frame 30-90 (1-3s):** Slow drift forward, new tree clusters enter frame; light shifts subtly
3. **Frame 90-150 (3-5s):** Camera continues drift; a wider gap reveals brighter sunlight pool below canopy

### Typography
- No on-screen text

### Easing
- N/A (live footage, no programmatic easing)

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={360} durationInFrames={150}>
  <Video src={veoClip("aerial_forest")} />
  <Audio src={narration("veo_section_002")} />
</Sequence>
```

## Data Points
```json
{
  "veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "clip_id": "aerial_forest",
  "audio_segment": "veo_section_002"
}
```

---
