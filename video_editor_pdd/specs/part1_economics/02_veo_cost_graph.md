[veo:part1_economics_veo_01] Cinematic Animated Cost Graph — Dual Lines Crossing

# Section 1.1: Veo Background — Animated Cost Graph

**Tool:** Veo
**Duration:** ~90s (used across Acts A, B, and returns in G)
**Timestamp:** 0:00 - 1:30 (primary), 6:15 - 6:22 (return)

## Visual Description
A cinematic 4K animated infographic background showing an elegant graph visualization on a dark surface. Two luminous lines — one representing "cost of patching" trending upward, the other "cost of generation" trending downward — draw themselves across the frame. The lines cross dramatically at a glowing intersection point. The aesthetic is inspired by 3Blue1Brown: mathematical precision meets cinematic beauty. The camera executes a slow push-in toward the graph, tightening from a medium-wide shot of the full visualization to a closer view of the data. In Act G (6:15), the footage is re-used with a dramatic zoom to the crossover point.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part1_economics_veo_01.mp4`
- Frame chain: none (first shot of Part 1)

### Visual Elements
- Environment: abstract dark studio or void — deep navy (#0F172A) background
- Graph surface: faintly glowing grid plane with perspective, receding into depth
- Line A (patching cost): warm amber/red (#EF4444 → #F59E0B gradient), trending upward left-to-right
- Line B (generation cost): cool blue/green (#3B82F6 → #22C55E gradient), trending downward left-to-right
- Intersection point: bright white/golden glow with particle burst effect
- Axis lines: subtle white at 20% opacity
- Data points: small glowing dots along each line that illuminate as the line passes through them

### Camera Motion
- Type: slow dolly-in (digital push)
- Start framing: medium-wide (full graph visible, ~80% of frame)
- End framing: medium (graph fills ~90% of frame, intersection near center)
- Speed: steady, ~1.5% zoom per second
- Act G return: faster push to intersection, ~5% zoom per second

### Veo Prompt
```
A cinematic 4K animated infographic on a dark navy background. Two luminous glowing lines
on an elegant graph — one amber/red trending upward, one blue/green trending downward —
cross at a dramatic glowing intersection point. Mathematical precision, 3Blue1Brown style.
Faintly glowing grid plane with perspective. Camera slowly pushes in toward the graph.
Particle effects at the intersection. Clean, modern data visualization aesthetic.
16:9 aspect ratio, film grain, shallow depth of field. No text overlays.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: cool blue shift (#1E3A5F tint)
- Highlights: warm glow at intersection (#F59E0B)
- Film grain: subtle, cinematic

## Narration Sync
> "Your grandmother figured out socks got cheap, and she stopped darning. Sometime in the late 1950s, the cost of materials — cotton, nylon, elastic — was higher than the cost of labor..."

This Veo clip serves as the background layer during Acts A and B (0:00-2:30), and returns in Act G (6:15-6:22).

## Composition Notes
- **Background layer** for Acts A-B and G
- Title card overlay (01_title_card.md) composited on top for first 5s
- Cost crossover chart overlay (03_cost_crossover_chart.md) composited as data layer
- Stat callout overlays appear on top during Act B
- Crossfades to 05_veo_debt_accumulation at ~2:30 mark
- Returns at 6:15 via crossfade for Act G finale
- Subtitle track (14_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part1_economics_veo_01.mp4",
  "duration_seconds": 90,
  "total_frames_at_30fps": 2700,
  "camera_motion": "dolly_in",
  "shot_type": "medium_wide_to_medium",
  "usage_windows": [
    {"act": "A-B", "start": "0:00", "end": "2:30"},
    {"act": "G", "start": "6:15", "end": "6:22"}
  ]
}
```

---
