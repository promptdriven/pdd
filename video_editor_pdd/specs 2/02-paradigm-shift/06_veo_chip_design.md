[veo:part2_paradigm_shift_veo_03] Chip Design Evolution — Hand-Drawn Gates to HDL Code

# Section 2.5: Veo Background — Chip Design Transition

**Tool:** Veo
**Duration:** ~45s (Act D)
**Timestamp:** 2:00 - 2:45

## Visual Description
A cinematic morph sequence showing the evolution of semiconductor design. The shot begins with a close-up of a hand-drawn integrated circuit layout on drafting paper — pencil lines on graph paper, rulers and erasers visible at the edges, warm incandescent desk lamp casting soft shadows. The hand-drawn schematic slowly transforms: the pencil lines begin glowing, lifting off the paper as luminous traces. The drafting paper dissolves away as the lines reorganize themselves into structured text — Verilog HDL code rendered as floating monospaced characters in cool blue. The code characters then collapse inward, forming an automated chip layout — a top-down view of a silicon die with colorful metal layers, perfectly aligned routing. The transition represents 40 years of progress: hand-craft → behavioral description → automated synthesis.

## Technical Specifications

### Canvas
- Resolution: 3840x2160 (4K), downscaled to 1920x1080 for composition
- Aspect ratio: 16:9
- Output: `veo/part2_paradigm_shift_veo_03.mp4`
- Frame chain: crossfade from `veo/part2_paradigm_shift_veo_02.mp4`

### Visual Elements
- Phase 1 — Hand-drawn (0-15s):
  - Environment: drafting desk, warm incandescent lighting
  - Paper: cream/off-white graph paper with blue grid lines
  - Drawings: pencil schematic of logic gates (AND, OR, NOT), interconnect lines
  - Props: wooden ruler, eraser shavings, pencil tips at edges
  - Mood: 1980s engineering workspace, nostalgic warmth
- Phase 2 — HDL transformation (15-30s):
  - Pencil lines glow blue-white, lifting off paper surface
  - Paper dissolves to black background
  - Lines reorganize into monospaced code blocks (Verilog syntax)
  - Code rendered as floating 3D text, #3B82F6 with subtle glow
  - Key visible text: `module`, `assign`, `always @(posedge clk)`
- Phase 3 — Silicon layout (30-45s):
  - Code characters collapse inward like magnetic particles
  - Form top-down silicon die view with colored metal layers
  - Layer colors: M1 #3B82F6, M2 #22C55E, M3 #F97316, substrate #1E293B
  - Perfect grid alignment, automated routing visible
  - Camera pushes in slightly to reveal fine detail

### Camera Motion
- Phase 1 (0-15s): Slight handheld drift over drafting paper, organic feel
  - Subtle 0.5° wobble, macro focus on gate drawings
- Phase 2 (15-30s): Stabilizes as lines lift, slow pull-back to see full code block
- Phase 3 (30-45s): Smooth push-in to silicon die, precision camera movement
  - Symbolizes: hand-made → machine-made transition in camera quality too

### Veo Prompt
```
Cinematic 4K morph sequence. Starts on close-up of hand-drawn integrated circuit
schematic on graph paper — pencil lines, logic gates, warm desk lamp lighting, 1980s
drafting table aesthetic. Pencil lines begin glowing blue-white and lift off the paper.
Paper dissolves to black as lines reorganize into floating Verilog HDL code in blue
monospaced text. Code characters then collapse inward, forming a top-down silicon chip
layout with colorful metal routing layers — blue, green, orange on dark substrate.
Camera transitions from handheld organic feel to precision digital movement.
16:9 aspect ratio, film grain, shallow depth of field. No text overlays.
```

### Color Grading
- Phase 1: warm tungsten (3200K), high contrast, cream paper whites
- Phase 2: transitional — warm desaturates, cool blue introduces
- Phase 3: cool precision, deep blacks, saturated neon layer colors
- Film grain: heavy in Phase 1 (analog feel), reduces through Phase 2-3

## Narration Sync
> "1980s — engineers hand-drew gate layouts. 1985 — Verilog HDL: describe behavior, not wires. Synopsys added verification with SAT and SMT solvers. Same revolution: specification replaced manual construction."

Hand-drawn phase plays during "engineers hand-drew gate layouts." HDL transformation begins on "Verilog HDL." Silicon layout forms on "verification" and "automated."

## Composition Notes
- **Background layer** for Act D
- Crossfade from 04_veo_value_migration (20 frames)
- HDL timeline overlay (07_hdl_timeline.md) composited on top
- Crossfades to 09_veo_prompt_to_code at ~2:45 mark
- Subtitle track (11_subtitle_track.md) runs over entire duration

## Data Points
```json
{
  "output": "veo/part2_paradigm_shift_veo_03.mp4",
  "duration_seconds": 45,
  "total_frames_at_30fps": 1350,
  "camera_motion": "handheld_to_precision",
  "shot_type": "macro_morph_sequence",
  "phases": [
    {"name": "hand_drawn", "start": "0:00", "end": "0:15", "camera": "handheld_drift", "era": "1980s"},
    {"name": "hdl_transform", "start": "0:15", "end": "0:30", "camera": "stabilize_pullback", "era": "1985"},
    {"name": "silicon_layout", "start": "0:30", "end": "0:45", "camera": "precision_push_in", "era": "1990s+"}
  ],
  "usage_windows": [
    {"act": "D", "start": "2:00", "end": "2:45"}
  ]
}
```

---
