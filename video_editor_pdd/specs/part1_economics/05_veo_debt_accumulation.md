[veo:part1_economics_veo_02] Technical Debt Accumulation — Stacking Layers

# Section 1.4: Veo Background — Technical Debt Accumulation

**Tool:** Veo
**Duration:** ~90s
**Timestamp:** 2:30 - 4:00

## Visual Description
A cinematic visualization of technical debt as physical layers accumulating. The scene opens on a clean, pristine code structure — translucent glass-like slabs stacked neatly, glowing with soft blue light. As the camera slowly tilts upward, new layers begin stacking on top — but each successive layer is darker, more opaque, and slightly misaligned. Cracks and red fracture lines appear in lower layers as weight accumulates. The mood shifts from clean and orderly to ominous and unstable. By the end, the tower of layers is visibly distressed — leaning, cracked, with red warning glows seeping through fractures.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part1_economics_veo_02.mp4`
- Frame chain: crossfade from `veo/part1_economics_veo_01.mp4`

### Visual Elements
- Environment: abstract dark void, deep navy (#0F172A)
- Initial layers: 4-6 translucent glass slabs, stacked vertically, soft blue glow (#3B82F6)
- Accumulating layers: progressively darker (blue → gray → dark red tint), slightly rotated/offset
- Fracture effects: red glowing cracks (#EF4444) in lower layers, appearing mid-sequence
- Particle effects: small debris fragments drifting from stressed areas
- Ambient light: cool blue from below, transitioning to ominous red/amber from above

### Camera Motion
- Type: slow tilt upward (following the growing stack)
- Start framing: medium shot of clean base layers
- End framing: wide shot revealing full unstable tower
- Speed: matched to layer accumulation rate
- Stabilization: perfectly smooth

### Veo Prompt
```
A cinematic 4K visualization of translucent glass-like data layers stacking vertically
in a dark void. Initially clean and organized with soft blue glow. As layers accumulate,
they become darker, misaligned, and cracked with red fracture lines. Camera slowly tilts
upward following the growing unstable tower. Ominous mood shift from clean to distressed.
Particle debris from stress fractures. Dark navy background, cinematic lighting. No text.
16:9 aspect ratio, shallow depth of field.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Early midtones: cool blue (#3B82F6 tint)
- Late midtones: shifting to warm danger (#EF4444 tint)
- Highlights: fracture glow (#EF4444 → #F59E0B)
- Film grain: subtle, cinematic

## Narration Sync
> "The dashed line — total cost — barely moves. That's the hidden story. GitHub's study: 55% speedup, but only on greenfield tasks... Uplevel tracked 800 developers... GitClear analyzed 211 million lines..."

This clip provides the atmospheric background during Act C, where the narration reveals hidden costs of AI-generated code.

## Composition Notes
- **Background layer** for Act C (2:30-4:00)
- Crossfade in from 02_veo_cost_graph at 2:30 (30 frames)
- Stat callout overlays (06_stat_callout_uplevel, 07_stat_callout_gitclear) appear on top
- Crossfades to 08_veo_context_window at ~4:00 mark
- Subtitle track (14_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part1_economics_veo_02.mp4",
  "duration_seconds": 90,
  "total_frames_at_30fps": 2700,
  "camera_motion": "tilt_up",
  "shot_type": "medium_to_wide",
  "mood_arc": "clean_to_ominous",
  "crossfade_in_from": "veo/part1_economics_veo_01.mp4",
  "crossfade_out_to": "veo/part1_economics_veo_03.mp4"
}
```

---
