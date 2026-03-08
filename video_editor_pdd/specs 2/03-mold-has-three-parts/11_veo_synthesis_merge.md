[veo:part3_mold_veo_06] Cinematic Three Components Merging Into Complete Mold

# Section 3.10: Veo Background — Synthesis Merge

**Tool:** Veo
**Duration:** ~15s (used during Synthesis)
**Timestamp:** 4:30 - 4:40 (with 5s buffer)

## Visual Description
A cinematic 4K visualization of three distinct colored energy streams converging into a single unified structure. From the left, a green stream (test capital) flows inward. From the top-right, a gold stream (prompt capital) arcs downward. From the bottom-right, a purple stream (grounding capital) curves upward. The three streams meet at center and merge into a single glowing white-gold mold structure that pulses with all three colors rippling through it. The merge point erupts in a brief, brilliant flash. The camera pushes in toward the merge point, tightening to a close-up of the unified mold as it solidifies. This is the visual climax of Part 3.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part3_mold_veo_06.mp4`
- Frame chain: crossfade from `part3_mold_veo_05`

### Visual Elements
- Environment: abstract dark void — deep navy (#0F172A)
- Green stream: flowing energy from left edge toward center, #22C55E
- Gold stream: flowing energy from upper-right toward center, #F59E0B
- Purple stream: flowing energy from lower-right toward center, #A855F7
- Merge point: center of frame, intense white-gold flash on convergence
- Unified mold: crystalline/metallic structure that forms at center after merge
  - Surface: iridescent, reflecting green/gold/purple
  - Shape: abstract but geometric — suggesting a precision mold or template
- Particle effects: burst of mixed-color particles at merge moment
- Post-merge glow: steady warm white light emanating from the unified structure

### Camera Motion
- Type: push-in toward merge point
- Start framing: wide shot (all three streams visible entering from edges)
- End framing: medium close-up on the unified mold structure
- Speed: accelerating — slow at start, faster during merge, settling after
- Dramatic timing: push-in accelerates at merge moment (~frame 150)

### Veo Prompt
```
A cinematic 4K visualization of three colored energy streams converging at center. A green
stream from the left, a gold stream from upper-right, and a purple stream from lower-right
flow toward a central merge point. At convergence, a brilliant white-gold flash creates a
crystalline mold structure that reflects all three colors. Particle burst at the merge point.
Camera pushes in toward the merge. Abstract dark navy void background. Dramatic, climactic
lighting. Shallow depth of field, film grain, 16:9 aspect ratio. No text overlays.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: balanced tricolor wash
- Highlights: brilliant white-gold at merge point (#FFF7ED)
- Post-merge: warm iridescent tones
- Film grain: subtle, cinematic

## Narration Sync
> "Prompt plus tests plus grounding equals intent plus constraints plus style equals a complete specification."

The three streams converge as the narrator lists the three components. The merge flash occurs on "complete specification."

## Composition Notes
- **Background layer** for Synthesis (4:30-4:40)
- Crossfades from 09_veo_grounding_loop (20-frame crossfade)
- 12_three_pillars_diagram.md composited as overlay during this clip
- Fade-out to black at final 30 frames (end of Part 3)
- Subtitle track (13_subtitle_track.md) runs to end

## Data Points
```json
{
  "output": "veo/part3_mold_veo_06.mp4",
  "duration_seconds": 15,
  "total_frames_at_30fps": 450,
  "camera_motion": "accelerating_push_in",
  "shot_type": "wide_to_medium_closeup",
  "merge_frame": 150,
  "streams": [
    {"name": "tests", "color": "#22C55E", "origin": "left"},
    {"name": "prompt", "color": "#F59E0B", "origin": "upper-right"},
    {"name": "grounding", "color": "#A855F7", "origin": "lower-right"}
  ],
  "usage_windows": [
    {"act": "Synthesis", "start": "4:30", "end": "4:40"}
  ]
}
```

---
