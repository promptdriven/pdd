[Remotion] Part 4: Precision Brings Cost

## Overview
- Composition ID: `Part4PrecisionTradeoff`
- Duration: ~96.91s (1:36, matches narration audio)
- Remotion dir: `S04-PrecisionTradeoff`
- Mood: trade-off exploration → pragmatism

## Visual Design
- Background: Veo-generated conceptual visualizations with Remotion overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), amber (#F59E0B), steel gray (#64748B), test green (#22C55E)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part4_precision/narration.wav`
- Word timestamps: `part4_precision/word_timestamps.json`
- Segments: `part4_precision_001` through `part4_precision_011`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "Precision Brings Cost"
- `veo_01_3d_printer_vs_mold.md` — 3D printer vs injection mold trade-off (10s)
- `veo_02_precision_curve.md` — cost vs precision U-curve graph (10s)
- `veo_03_embedded_code.md` — code examples at different precision levels (10s)
- `veo_04_spectrum_slider.md` — interactive spectrum visualization (10s)
- `stat_callout_prompt_compression.md` — prompt compression stat
- `split_prompt_detail_vs_tests.md` — split screen: prompt detail vs test coverage

## Narrative Arc & Shot Breakdown

### Title Card (0:00–0:05)
- Title card overlay: "Precision Brings Cost"
- Veo source: `part4_precision_veo_01` (3D printer starting)
- Overlay: title card with amber accent
- Transition: fade-in from black (30 frames)

### Act A — The Trade-Off (0:05–0:30)
- Narration: Precision has a cost. More detailed prompts mean slower generation. More comprehensive tests mean longer feedback cycles. This is the trade-off.
- Veo source: `part4_precision_veo_01` (3D printer vs mold)
- Overlays:
  - Split: prompt detail vs tests at ~0:25
  - Stat callout — prompt compression at ~0:26
- Camera: side-by-side comparison of 3D printer (slow, precise) vs injection mold (fast, constrained)
- Transition: crossfade from title card

### Act B — The Curve (0:30–1:00)
- Narration: There's a sweet spot between vagueness and over-specification. Too little precision — AI hallucinates. Too much — you're writing the code yourself. The U-curve has a minimum.
- Veo source: `part4_precision_veo_02` (precision curve)
- Camera: animated U-curve drawing with sweet spot highlighted
- Transition: crossfade from Act A (20 frames)

### Act C — Practical Spectrum (1:00–1:36)
- Narration: Adjust precision based on context. Greenfield project? Lighter prompts, explore fast. Legacy system with strict contracts? Heavy test walls, precise prompts. The spectrum is a tool, not a rule.
- Veo sources: `part4_precision_veo_03` → `part4_precision_veo_04`
- Camera: code examples morph into spectrum slider
- Transition: crossfade between veo_03 and veo_04 (20 frames), fade-out to black at end (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across acts
  - `veo/part4_precision_veo_01.mp4` (Title + Act A)
  - `veo/part4_precision_veo_02.mp4` (Act B)
  - `veo/part4_precision_veo_03.mp4` (Act C start)
  - `veo/part4_precision_veo_04.mp4` (Act C end)
- Title card overlay (see `title_card.md`)
- Stat callout overlay synced to narration (see `stat_callout_prompt_compression.md`)
- Split screen overlay (see `split_prompt_detail_vs_tests.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
