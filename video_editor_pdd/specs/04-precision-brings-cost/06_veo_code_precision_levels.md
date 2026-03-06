[veo:part4_precision_veo_03] Cinematic Code at Different Precision Levels

# Section 4.5: Veo Background — Code at Different Precision Levels

**Tool:** Veo
**Duration:** ~20s (used in Act C start)
**Timestamp:** 1:00 - 1:20

## Visual Description
A cinematic view of a large curved monitor displaying code at different levels of precision, cross-fading between them. The first state shows sparse, vague pseudocode with wide spacing and minimal comments — representing "lighter prompts, explore fast." The code then morphs/cross-fades into a dense, heavily-annotated codebase with strict type annotations, contract assertions, and comprehensive docstrings — representing "heavy test walls, precise prompts." The camera is positioned over-the-shoulder of a developer silhouette, slowly arcing around the screen. The environment has moody, focused lighting — a single desk lamp illuminating the keyboard while the monitor casts blue-white light on the scene.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part4_precision_veo_03.mp4`
- Frame chain: crossfade from `veo/part4_precision_veo_02.mp4`

### Visual Elements
- Environment: developer workspace, dark moody lighting, single desk lamp
- Monitor: large curved ultrawide displaying code
- Code state 1 (first 10s): sparse pseudocode, wide line spacing, minimal structure
- Code state 2 (last 10s): dense annotated code, tight spacing, visible type hints and assertions
- Developer: silhouette only, seated, slightly out of focus
- Ambient: subtle keyboard backlight glow, monitor edge lighting

### Camera Motion
- Type: slow arc from left shoulder to slightly right of center
- Start framing: over-left-shoulder view of monitor
- End framing: slightly more frontal, emphasizing code density change
- Speed: steady, ~2° arc per second
- Duration: 20 seconds of usable footage

### Veo Prompt
```
Cinematic 4K over-the-shoulder shot of a developer silhouette at a curved ultrawide monitor.
The screen displays code that transitions from sparse, vague pseudocode to dense, heavily
annotated code with type annotations and assertions. Dark moody workspace, single desk lamp,
monitor casting blue-white light. Camera slowly arcs from left shoulder toward center.
Shallow depth of field, atmospheric, focused. 16:9, film grain. No text overlays.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: cool blue from monitor light (#1E3A5F)
- Highlights: warm amber from desk lamp (#F59E0B tint)
- Film grain: subtle, cinematic

## Narration Sync
> "Adjust precision based on context. Greenfield project? Lighter prompts, explore fast. Legacy system with strict contracts? Heavy test walls, precise prompts."

Sparse code visible during "lighter prompts, explore fast." Dense annotated code visible during "heavy test walls, precise prompts."

## Composition Notes
- **Background layer** for Act C start (1:00-1:20)
- Crossfades from Veo 02 (precision curve) at ~1:00
- Spectrum slider overlay (07_spectrum_slider.md) composited on top during this segment
- Crossfades to 08_veo_spectrum_exploration at ~1:20
- Subtitle track (09_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part4_precision_veo_03.mp4",
  "duration_seconds": 20,
  "total_frames_at_30fps": 600,
  "camera_motion": "arc_left_to_center",
  "shot_type": "over_shoulder_to_frontal",
  "usage_windows": [
    {"act": "C-start", "start": "1:00", "end": "1:20"}
  ]
}
```

---
