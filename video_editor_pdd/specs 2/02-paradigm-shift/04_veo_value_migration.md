[veo:part2_paradigm_shift_veo_02] Abstract Value Migration — Physical Object to Blueprint

# Section 2.3: Veo Background — Value Migration Visualization

**Tool:** Veo
**Duration:** ~30s (Act C)
**Timestamp:** 1:30 - 2:00

## Visual Description
An abstract cinematic visualization of value migrating from physical object to specification. The shot opens on a translucent plastic part sitting on a dark reflective surface — glowing faintly, but dimming. Luminous particles of golden light begin lifting from the object, rising upward in graceful spiraling arcs like embers from a dying fire. The camera tilts upward, following the particles as they coalesce into a glowing blueprint/schematic floating above — clean geometric lines forming the outline of the mold specification. The physical part below fades to near-invisibility while the blueprint above intensifies, becoming crisp and brilliant. The visual metaphor is unmistakable: the value has migrated from the thing to its design.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part2_paradigm_shift_veo_02.mp4`
- Frame chain: crossfade from `veo/part2_paradigm_shift_veo_01.mp4`

### Visual Elements
- Environment: dark abstract void, reflective floor plane
- Physical part: translucent white/cream plastic component, centered at frame bottom third
- Particles: golden luminous orbs (#F59E0B → #FBBF24), 50-100 particles rising
- Spiral motion: particles follow logarithmic spiral paths upward
- Blueprint: geometric line drawing, #3B82F6 neon glow on dark background
- Blueprint lines: thin (1-2px), precise, technical drawing aesthetic
- Reflective surface: dark (#0F172A) with subtle mirror effect

### Camera Motion
- Phase 1 (0-10s): Static on physical part, particles begin rising
- Phase 2 (10-25s): Slow tilt upward following particles, revealing blueprint
- Phase 3 (25-30s): Settle on blueprint fully formed, slight push-in
- Speed: smooth, 1° tilt per second

### Veo Prompt
```
Abstract cinematic 4K visualization of value migrating upward. A translucent white
plastic part sits on a dark reflective surface, dimming. Golden luminous particles lift
from the object, spiraling upward in graceful arcs like embers. Camera tilts up to follow.
Particles coalesce into a glowing blue neon blueprint schematic floating above — clean
geometric technical drawing lines. Physical part fades to near-invisible while blueprint
intensifies. Dark void environment, reflective floor, shallow depth of field. Ethereal
and abstract. 16:9 aspect ratio, film grain. No text overlays.
```

### Color Grading
- Shadows: deep black (#000000) with navy lift (#0F172A)
- Midtones: cool blue shift for blueprint region
- Highlights: warm gold for particles, cool blue for blueprint
- Film grain: light, ethereal quality

## Narration Sync
> "Value migrates from the object to the specification. The plastic part is disposable. The mold is everything."

Particles begin rising as "value migrates" is spoken. Blueprint fully forms as "the mold is everything" lands.

## Composition Notes
- **Background layer** for Act C
- Crossfade from 02_veo_injection_molding (20 frames)
- Value migration diagram overlay (05_value_migration_diagram.md) composited on top
- Crossfades to 06_veo_chip_design at ~2:00 mark
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part2_paradigm_shift_veo_02.mp4",
  "duration_seconds": 30,
  "total_frames_at_30fps": 900,
  "camera_motion": "tilt_up",
  "shot_type": "static_to_tilt",
  "phases": [
    {"name": "part_dimming", "start": "0:00", "end": "0:10", "motion": "static"},
    {"name": "particle_follow", "start": "0:10", "end": "0:25", "motion": "tilt_up"},
    {"name": "blueprint_settle", "start": "0:25", "end": "0:30", "motion": "push_in"}
  ],
  "usage_windows": [
    {"act": "C", "start": "1:30", "end": "2:00"}
  ]
}
```

---
