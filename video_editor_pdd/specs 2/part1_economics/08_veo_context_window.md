[veo:part1_economics_veo_03] Context Window Degradation — Shrinking Visualization

# Section 1.7: Veo Background — Context Window Degradation

**Tool:** Veo
**Duration:** ~75s
**Timestamp:** 4:00 - 5:15

## Visual Description
A cinematic visualization of AI capability degrading as context grows. The scene begins with a bright, expansive holographic display — a luminous rectangular "window" floating in dark space, filled with clearly readable flowing code. The window is sharp, vibrant, and full of life. As the sequence progresses, the window fills with more and more content — lines of code pack in tighter, the glow dims, edges blur, and the window itself appears to compress and distort. The code becomes illegible, colors desaturate, and static/noise artifacts creep in from the edges. The visual metaphor is clear: the more you stuff into the window, the worse everything gets.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part1_economics_veo_03.mp4`
- Frame chain: crossfade from `veo/part1_economics_veo_02.mp4`

### Visual Elements
- Environment: abstract dark void, deep navy (#0F172A)
- Context window: luminous rectangular hologram, ~60% of frame width initially
- Code content: flowing lines of syntax-highlighted code (blues, greens, whites)
- Early state: sharp edges, vivid colors, readable code, strong glow
- Mid state: window packed full, text shrinking, edges softening
- Late state: edges distorting with chromatic aberration, color desaturation, noise/static artifacts
- Particle effects: small data fragments breaking off edges in late state

### Camera Motion
- Type: slow push-in, then subtle pull-back as distortion increases
- Start framing: medium (window centered, comfortable negative space)
- Mid framing: tighter (window fills more frame as content grows)
- End framing: slightly pulled back (revealing the full distorted mess)
- Speed: steady, ~1% shift per second

### Veo Prompt
```
A cinematic 4K visualization of a luminous holographic rectangular window floating in
dark space, filled with flowing syntax-highlighted code. Initially sharp and vibrant.
Over time, the window fills with more code, becoming packed and compressed. Colors
desaturate, edges blur and distort with chromatic aberration, static noise artifacts
appear. The code becomes illegible as the window degrades. Small data particle fragments
break off the edges. Dark navy void background. Camera slowly pushes in then pulls back.
Cinematic lighting, 16:9 aspect ratio, no text overlays.
```

### Color Grading
- Early: vibrant blues and greens (#3B82F6, #22C55E), sharp contrast
- Mid: desaturation begins, contrast flattening
- Late: heavy desaturation, red/amber distortion tint (#EF4444 chromatic fringe)
- Film grain: increasing from subtle to heavy (tracking degradation)

## Narration Sync
> "Small codebase — AI is brilliant. Large codebase — performance degrades. EMNLP research showed 14 to 85 percent capability loss as context windows fill."

The visual degradation tracks the narration — starting clean as small codebases are discussed, filling and distorting as the context window problem is explained.

## Composition Notes
- **Background layer** for Acts D-E (4:00-5:45)
- Crossfade in from 05_veo_debt_accumulation at 4:00 (30 frames)
- Context degradation chart overlay (09_context_degradation_chart.md) composited on top
- Split screen overlay (10_split_perception_reality.md) appears during Act E
- Crossfades to 11_veo_regeneration_pipeline at ~5:45 mark
- Subtitle track (14_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part1_economics_veo_03.mp4",
  "duration_seconds": 75,
  "total_frames_at_30fps": 2250,
  "camera_motion": "push_in_then_pull_back",
  "shot_type": "medium_to_tight_to_medium",
  "degradation_arc": [
    {"percent": 0, "state": "clean_sharp_vibrant"},
    {"percent": 30, "state": "filling_slightly_compressed"},
    {"percent": 60, "state": "packed_desaturating_softening"},
    {"percent": 100, "state": "distorted_noisy_illegible"}
  ],
  "crossfade_in_from": "veo/part1_economics_veo_02.mp4",
  "crossfade_out_to": "veo/part1_economics_veo_04.mp4"
}
```

---
