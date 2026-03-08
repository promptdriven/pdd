[veo:part2_paradigm_shift_veo_01] Cinematic Injection Molding Process — Molten Material into Precision Mold

# Section 2.1: Veo Background — Injection Molding Process

**Tool:** Veo
**Duration:** ~90s (used across Acts A and B)
**Timestamp:** 0:00 - 1:30

## Visual Description
A cinematic 4K shot of an industrial injection molding process. The camera opens on a macro view of molten plastic — glowing amber-orange, viscous, and luminous — flowing into a precision steel mold. The mold is rendered in cool steel tones with sharp machined edges, catching highlights from the furnace glow. As the material fills the cavity, the camera pulls back to reveal a production line: identical perfectly-formed parts emerging one after another in rapid succession. The aesthetic blends industrial documentary with abstract beauty — shallow depth of field isolates the flowing material while the background recedes into a warm bokeh. In the second half, the camera continues pulling back to show dozens of identical parts on a conveyor, emphasizing the "design once, produce unlimited" principle.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part2_paradigm_shift_veo_01.mp4`
- Frame chain: none (first shot of Part 2)

### Visual Elements
- Environment: industrial manufacturing facility, dark ambient lighting with warm accent
- Molten material: glowing amber-orange (#F97316 → #EF4444), viscous fluid dynamics
- Steel mold: cool metallic (#94A3B8 → #CBD5E1), precision-machined with sharp edges
- Production line: identical white/cream parts emerging on dark conveyor
- Ambient lighting: warm furnace glow from left, cool overhead fluorescents
- Atmospheric haze: subtle industrial steam/vapor for depth

### Camera Motion
- Phase 1 (0-45s): Extreme macro — molten material flowing, slow push-in
  - Start: ECU on material flow, shallow DOF (f/1.8 equivalent)
  - Motion: slight crane down, following material into mold cavity
- Phase 2 (45-90s): Pull-back reveal — production line of identical parts
  - Transition: smooth dolly-out from mold to wide shot
  - End: medium-wide showing conveyor of identical parts
  - Speed: steady, ~2% zoom-out per second

### Veo Prompt
```
Cinematic 4K macro shot of industrial injection molding. Glowing amber-orange molten
plastic flowing into a precision steel mold with sharp machined edges. Camera starts
extreme close-up on viscous flowing material, shallow depth of field, warm furnace
lighting. Slowly pulls back to reveal production line of identical white plastic parts
emerging on a dark conveyor belt. Industrial documentary aesthetic with abstract beauty.
Atmospheric steam, film grain, warm color grading. 16:9 aspect ratio. No text overlays.
```

### Color Grading
- Shadows: deep navy (#0F172A) with warm lift
- Midtones: warm amber shift (#92400E tint)
- Highlights: molten orange (#F97316) on material, cool steel (#CBD5E1) on mold
- Film grain: moderate, industrial documentary feel

## Narration Sync
> "Not cheaper materials — a shift in how things are made. The same pattern across textiles, plastics, semiconductors. The value didn't stay in the thing itself. Design the mold once, produce unlimited identical parts. Find a defect? Fix the mold — not every individual part. The cost is in the specification, not the production."

This Veo clip serves as the background layer during Acts A (0:00-0:45) and B (0:45-1:30). Title card overlays for first 5 seconds, then mold infographic and subtitle track overlay on top.

## Composition Notes
- **Background layer** for Acts A-B
- Title card overlay (01_title_card.md) composited on top for first 5s
- Mold production infographic (03_mold_production_infographic.md) overlaid during Act B
- Crossfades to 04_veo_value_migration at ~1:30 mark
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part2_paradigm_shift_veo_01.mp4",
  "duration_seconds": 90,
  "total_frames_at_30fps": 2700,
  "camera_motion": "macro_to_pullback",
  "shot_type": "extreme_closeup_to_medium_wide",
  "phases": [
    {"name": "macro_flow", "start": "0:00", "end": "0:45", "motion": "push_in_crane_down"},
    {"name": "pullback_reveal", "start": "0:45", "end": "1:30", "motion": "dolly_out"}
  ],
  "usage_windows": [
    {"act": "A", "start": "0:00", "end": "0:45"},
    {"act": "B", "start": "0:45", "end": "1:30"}
  ]
}
```

---
