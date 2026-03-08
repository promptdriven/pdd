[veo:part4_precision_veo_01] Cinematic 3D Printer vs Injection Mold Trade-Off

# Section 4.1: Veo Background — 3D Printer vs Injection Mold

**Tool:** Veo
**Duration:** ~30s (used across Title Card and Act A)
**Timestamp:** 0:00 - 0:30

## Visual Description
A cinematic side-by-side comparison of two manufacturing processes that embodies the precision-vs-speed trade-off. On the left, a 3D printer meticulously deposits material layer by layer — slow, precise, custom. On the right, an injection mold machine rapidly stamps out identical parts — fast, constrained, mass-produced. The camera starts wide showing both processes, then slowly pushes in toward the 3D printer side as the narration emphasizes the cost of precision. Warm amber lighting on the 3D printer side, cool blue-steel on the mold side. The aesthetic is cinematic industrial — shallow depth of field, dramatic rim lighting, particles of material catching the light.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part4_precision_veo_01.mp4`
- Frame chain: none (first shot of Part 4)

### Visual Elements
- Environment: industrial workshop or abstract factory floor, dark moody lighting
- Left side (3D printer): warm amber/orange lighting (#F59E0B tones), slow deliberate motion
- Right side (injection mold): cool steel blue (#64748B tones), rapid repetitive motion
- Particles: fine material dust/filament catching rim light
- Surface: dark matte industrial (#1E293B)

### Camera Motion
- Type: slow dolly-in with subtle pan left
- Start framing: wide (both processes visible, ~80% of frame)
- End framing: medium-close on 3D printer (fills ~60% of frame)
- Speed: steady, ~1% zoom per second
- Duration: 30 seconds of usable footage

### Veo Prompt
```
Cinematic 4K side-by-side comparison of two manufacturing processes. Left: a 3D printer
meticulously building an object layer by layer with warm amber lighting, slow and precise.
Right: an injection mold machine rapidly stamping identical parts with cool steel-blue lighting,
fast and constrained. Dark industrial setting, shallow depth of field, dramatic rim lighting,
fine particles catching the light. Camera slowly pushes in toward the 3D printer. Moody,
atmospheric, documentary-style. 16:9, film grain. No text overlays.
```

### Color Grading
- Shadows: deep navy (#0F172A)
- Midtones: split-tone — amber left (#F59E0B), steel blue right (#64748B)
- Highlights: warm rim light on edges
- Film grain: subtle, cinematic

## Narration Sync
> "Precision has a cost. More detailed prompts mean slower generation. More comprehensive tests mean longer feedback cycles. This is the trade-off."

This Veo clip serves as the background layer during the Title Card (0:00-0:05) and Act A (0:05-0:30). Title card overlay composited on top for first 5s. The 3D printer slow-build visualizes "precision has a cost" while the mold visualizes the fast-but-constrained alternative.

## Composition Notes
- **Background layer** for Title Card + Act A
- Title card overlay (01_title_card.md) composited on top for first 5s
- Split screen overlay (05_split_prompt_detail_vs_tests.md) appears at ~0:20
- Stat callout overlay (04_stat_callout_prompt_compression.md) appears at ~0:22
- Crossfades to 06_veo_code_precision_levels at ~0:30 mark
- Subtitle track (09_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part4_precision_veo_01.mp4",
  "duration_seconds": 30,
  "total_frames_at_30fps": 900,
  "camera_motion": "dolly_in_pan_left",
  "shot_type": "wide_to_medium_close",
  "usage_windows": [
    {"act": "Title+A", "start": "0:00", "end": "0:30"}
  ]
}
```

---
