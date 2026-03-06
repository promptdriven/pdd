[veo:part5_compound_veo_02] Cinematic Compound Debt Accumulation Curves

# Section 5.3: Veo Background — Compound Debt Curves

**Tool:** Veo
**Duration:** ~25s (used across Act B)
**Timestamp:** 0:25 - 0:50

## Visual Description
A cinematic 4K visualization of two luminous curves drawing themselves in a vast dark space. The first curve — representing patching — is a red-orange line that climbs steeply upward in an exponential arc, leaving a trail of glowing debt particles that accumulate below it like digital sediment. The second curve — representing generation — is a green line that stays remarkably flat, periodically resetting to baseline with brief downward pulses (representing fresh regeneration cycles). The camera slowly tracks from left to right as time progresses, following the curves as they diverge. The visual gap between the two lines grows dramatically wider, filled with an increasingly dense red haze of accumulated debt.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part5_compound_veo_02.mp4`
- Frame chain: crossfade from `part5_compound_veo_01`

### Visual Elements
- Environment: abstract dark void — deep navy (#0F172A) with faint horizontal grid
- Floor/base plane: faintly glowing grid, #1E293B at 10% opacity
- Patching curve: bright red-orange line (#EF4444), thick luminous stroke, exponential climb
- Patching trail: red particle sediment accumulating below the climbing line, like digital dust
- Generation curve: bright green line (#22C55E), thin luminous stroke, stays near baseline
- Generation resets: brief green pulse flashes at regular intervals along the flat line
- Gap fill: red-orange volumetric haze between the two curves, density increasing left to right
- Time axis: subtle white markers along the bottom, suggesting months/years progression
- Ambient particles: floating dust motes with red and green tints

### Camera Motion
- Type: slow tracking shot, left to right (following time axis)
- Start framing: medium-wide, both curves visible at origin
- End framing: medium, focused on the widening gap between diverged curves
- Speed: steady, matching the narrative pace of debt accumulation
- Stabilization: smooth, mechanical dolly feel

### Veo Prompt
```
A cinematic 4K visualization of two luminous curves drawing themselves in a dark void.
One bright red-orange line climbs steeply upward in an exponential arc with glowing particle
debris accumulating below it. A second bright green line stays remarkably flat near the baseline,
with periodic brief downward reset pulses. The gap between the two lines grows dramatically wider,
filled with increasingly dense red-orange volumetric haze. Slow left-to-right tracking camera.
Dark navy environment with faint grid floor. Cinematic studio lighting, shallow depth of field,
film grain. No text overlays. 16:9 aspect ratio.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: neutral with slight warm bias in the gap zone
- Highlights: red-orange on patching curve, green on generation curve
- Film grain: subtle, cinematic

## Narration Sync
> "Patching accumulates debt linearly — each patch adds residual complexity. Generation resets debt each cycle — fresh code, no residue. The gap compounds."

This Veo clip serves as the background layer during Act B (0:25-0:50).

## Composition Notes
- **Background layer** for Act B
- Chart overlay (06_compound_debt_chart.md) composited on top for precise data visualization
- Stat callout overlay (05_stat_callout_cisq.md) appears on top at ~0:32
- Crossfades from 02_veo_maintenance_pie at ~0:25
- Crossfades to 07_veo_diverging_trajectories at ~0:50
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part5_compound_veo_02.mp4",
  "duration_seconds": 25,
  "total_frames_at_30fps": 750,
  "camera_motion": "tracking_left_to_right",
  "shot_type": "medium_wide_to_medium",
  "usage_windows": [
    {"act": "B", "start": "0:25", "end": "0:50"}
  ]
}
```

---
