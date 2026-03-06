[veo:part3_mold_veo_02] Cinematic Ratchet Mechanism — Tests Accumulate

# Section 3.4: Veo Background — Ratchet Effect

**Tool:** Veo
**Duration:** ~60s (used across Act A middle)
**Timestamp:** 1:00 - 2:00

## Visual Description
A cinematic 4K visualization of a mechanical ratchet mechanism — a gear that clicks forward and cannot turn back. Each tooth of the gear represents a test that has been added. As new teeth click into place, the gear advances with a satisfying mechanical precision. The ratchet sits on a dark surface with dramatic side-lighting, casting long shadows. Green energy pulses along the gear teeth as each one locks in. The camera slowly tightens from a medium shot to a close-up of the ratchet pawl engaging the next tooth, emphasizing irreversibility. The metaphor: once a test is written, the mold only gets more precise — it never loosens.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part3_mold_veo_02.mp4`
- Frame chain: crossfade from `part3_mold_veo_01`

### Visual Elements
- Environment: dark studio with dramatic side-lighting from left
- Ratchet gear: metallic surface with green luminous accents (#22C55E)
- Gear teeth: each tooth subtly labeled (implied test names, not readable)
- Pawl/spring: mechanical catch that prevents backward rotation
- Green energy: luminous pulse along each tooth as it locks — #22C55E glow
- Shadows: long, dramatic, cast to the right
- Surface: dark brushed metal or stone — #1A1A2E

### Camera Motion
- Type: slow push-in with slight downward tilt
- Start framing: medium shot (full ratchet visible, ~70% of frame)
- End framing: close-up (pawl and 3-4 teeth fill frame)
- Speed: steady, ~2% zoom per second

### Veo Prompt
```
A cinematic 4K visualization of a large mechanical ratchet gear mechanism on a dark surface.
Metallic gear with green luminous accents clicking forward one tooth at a time. A pawl
mechanism prevents backward rotation. Green energy pulses along gear teeth as each one locks
into place. Dramatic side-lighting from left, long shadows cast to the right. Camera slowly
pushes in from medium shot to close-up of the pawl engaging. Mechanical precision, industrial
beauty. Dark studio, brushed metal surface. 16:9 aspect ratio, film grain, shallow depth of
field. No text overlays.
```

### Color Grading
- Shadows: deep charcoal (#1A1A2E)
- Midtones: cool steel blue (#2D3748 tint)
- Highlights: test green (#22C55E) on gear edges
- Film grain: moderate, industrial feel

## Narration Sync
> "Every test you write is a ratchet click — the mold gets more precise, and it never goes backward. You're accumulating test capital."

This Veo clip serves as background during the middle portion of Act A, covering the ratchet metaphor narration.

## Composition Notes
- **Background layer** for Act A (1:00-2:00)
- Crossfades from 02_veo_test_walls (20-frame crossfade)
- Stat callout overlays may still be visible during early portion
- 10_ratchet_infographic.md composited as data overlay during this clip
- Crossfades to 06_split_prompt_vs_code or next veo clip at ~2:00
- Subtitle track (13_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part3_mold_veo_02.mp4",
  "duration_seconds": 60,
  "total_frames_at_30fps": 1800,
  "camera_motion": "push_in",
  "shot_type": "medium_to_closeup",
  "usage_windows": [
    {"act": "A-mid", "start": "1:00", "end": "2:00"}
  ]
}
```

---
