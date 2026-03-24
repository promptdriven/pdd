[veo:]

# Section 2.6: Aerial Forest Canopy Cutaway

**Tool:** Veo 3.1
**Duration:** ~4s
**Timestamp:** 0:12 – 0:16

## Visual Description
Aerial drone footage looking straight down at a dense green forest canopy. Sunlight filters through gaps in the leaves, creating dappled patterns of golden light on the darker foliage below. The camera drifts slowly, revealing the organic fractal patterns of treetops. Deep emerald greens dominate with warm golden highlights. A sense of scale and tranquility. No text overlay — pure cinematic B-roll.

## Technical Specifications

### Canvas
- Resolution: 1920×1080 (16:9)
- Background: N/A (full-bleed video)
- No grid lines

### Chart/Visual Elements
- **Source Clip:** `veo/05_veo_cutaway.mp4`
- **Veo Prompt:** "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves"
- **Color Grade:** Rich greens with warm golden sun flares; slightly desaturated shadows
- **Motion:** Slow overhead drift, subtle parallax as canopy layers shift

### Animation Sequence
1. **Frame 0–10 (0–0.33s):** Clip begins — camera already in motion overhead. Crossfade from previous composition.
2. **Frame 10–100 (0.33–3.33s):** Main footage — continuous aerial drift over forest canopy. Sunlight plays across leaf surfaces.
3. **Frame 100–120 (3.33–4.0s):** Footage continues to natural end. Prepare for transition to next composition.

### Typography
- None — pure cinematic footage

### Easing
- Crossfade-in: `linear`

## Narration Sync
> "It uses Veo-generated clips with narration overlay."

## Code Structure (Remotion)
```typescript
<Sequence from={0} durationInFrames={120}>
  <OffthreadVideo
    src={staticFile('veo_section/veo/05_veo_cutaway.mp4')}
    style={{ width: '100%', height: '100%', objectFit: 'cover' }}
  />
</Sequence>
```

## Data Points
```json
{
  "source": "veo/05_veo_cutaway.mp4",
  "veo_prompt": "An aerial drone shot of a green forest canopy with sunlight filtering through the leaves",
  "duration_seconds": 4.0,
  "veo_model": "veo-3.1-generate-001"
}
```

---
