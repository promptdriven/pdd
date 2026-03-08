[veo:part5_compound_veo_01] Cinematic Maintenance Cost Pie Chart Formation

# Section 5.1: Veo Background — Maintenance Pie Chart

**Tool:** Veo
**Duration:** ~25s (used across Title Card and Act A)
**Timestamp:** 0:00 - 0:25

## Visual Description
A cinematic 4K visualization of a massive luminous pie chart forming in a dark void. The chart materializes as glowing segments that rotate into position — one enormous segment dominates 85% of the circle in deep red (#EF4444), labeled "MAINTENANCE" in floating 3D text. The remaining thin slices — "Features," "Launch," "Infrastructure" — glow in muted blue, green, and amber respectively. The camera starts wide, then slowly dollies in toward the overwhelming maintenance slice. Volumetric light rays emanate from the seams between segments. The effect is visceral: the viewer feels the weight of maintenance cost crushing everything else.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part5_compound_veo_01.mp4`
- Frame chain: none (first shot of Part 5)

### Visual Elements
- Environment: abstract dark void — deep navy (#0F172A) with subtle floor reflection
- Floor plane: faintly reflective, dark navy with subtle red ambient glow
- Pie chart: 3D floating disc, ~600px apparent diameter, tilted ~30° toward camera
- Maintenance slice: 85% arc, deep red (#EF4444) with inner glow, volumetric light at edges
- Features slice: 7% arc, muted blue (#3B82F6) at 60% brightness
- Launch slice: 5% arc, muted green (#22C55E) at 60% brightness
- Infrastructure slice: 3% arc, muted amber (#F59E0B) at 60% brightness
- Segment seams: bright white-orange volumetric light rays leaking through gaps
- Floating particles: red-tinted dust motes drifting in ambient light

### Camera Motion
- Type: slow dolly-in with slight crane down
- Start framing: wide, entire chart visible with surrounding void, ~45° elevation
- End framing: medium-close on maintenance slice, ~30° elevation
- Speed: steady, ~2% zoom per second
- Stabilization: locked, smooth mechanical movement

### Veo Prompt
```
A cinematic 4K visualization of a massive glowing 3D pie chart forming in a dark void.
The chart is tilted toward the camera with one enormous dominant red segment taking up 85%
of the circle. Small thin slices in blue, green, and amber fill the remaining arc. Volumetric
light rays leak through the seams between segments. The dominant red slice glows with inner
radiance. Slow dolly-in camera movement from wide to medium-close. Dark studio environment,
deep navy background, reflective floor. Cinematic lighting, shallow depth of field, film grain.
No text overlays. 16:9 aspect ratio.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: warm red shift for maintenance dominance
- Highlights: red-orange glow on primary slice edges
- Film grain: subtle, cinematic

## Narration Sync
> "Eighty to ninety percent of software cost is maintenance. Not features. Not launch. Maintenance. This is the elephant in the room."

This Veo clip serves as the background layer during the Title Card (0:00-0:05) and Act A (0:05-0:25).

## Composition Notes
- **Background layer** for Title Card and Act A
- Title card overlay (01_title_card.md) composited on top for first 5s
- Stat callout overlay (03_stat_callout_maintenance.md) appears on top during this clip at ~0:18
- Crossfades to 04_veo_compound_debt_curve at ~0:25 mark
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part5_compound_veo_01.mp4",
  "duration_seconds": 25,
  "total_frames_at_30fps": 750,
  "camera_motion": "dolly_in_crane_down",
  "shot_type": "wide_to_medium_close",
  "usage_windows": [
    {"act": "Title+A", "start": "0:00", "end": "0:25"}
  ]
}
```

---
