[Remotion] Part 3: The Mold Has Three Parts

## Overview
- Composition ID: `Part3MoldThreeParts`
- Duration: ~280.73s (4:40, matches narration audio)
- Remotion dir: `S03-MoldThreeParts`
- Mood: grounded precision → intellectual excitement → synthesis

## Visual Design
- Background: Veo-generated conceptual visualizations with Remotion data overlays
- Color palette: dark navy (#0F172A), test green (#22C55E), prompt gold (#F59E0B), grounding purple (#A855F7), vibrant blue (#3B82F6)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part3_mold/narration.wav`
- Word timestamps: `part3_mold/word_timestamps.json`
- Segments: `part3_mold_001` through `part3_mold_025`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "The Mold Has Three Parts"
- `veo_01_test_walls.md` — test constraints building as walls (10s)
- `veo_02_ratchet_mechanism.md` — ratchet effect: tests accumulate, never go back (10s)
- `veo_03_z3_proof.md` — Z3 SMT solver mathematical proof visualization (10s)
- `veo_04_prompt_radiating.md` — prompt specification radiating into code variants (10s)
- `veo_05_grounding_loop.md` — grounding learning loop visualization (10s)
- `veo_06_synthesis_merge.md` — three components merging into complete mold (10s)
- `stat_callout_coderabbit.md` — CodeRabbit: AI code 1.7x more issues
- `stat_callout_dora.md` — DORA: AI without tests = instability
- `stat_callout_nl_context.md` — NL context improved code generation 41%
- `split_prompt_vs_code.md` — split screen: prompt spec vs generated code

## Narrative Arc & Shot Breakdown

### Title Card (0:00–0:05)
- Title card overlay: "The Mold Has Three Parts"
- Veo source: `part3_mold_veo_01` (test walls starting to build)
- Overlay: title card with tricolor accent (green/gold/purple)
- Transition: fade-in from black (30 frames)

### Act A — Test Capital (0:05–2:30)
- Narration: Tests are the walls of the mold — constraints that code cannot cross. CodeRabbit: AI code has 1.7x more issues, 75% logic errors, 8x perf problems. DORA: AI without tests = instability; with tests = delivery amplification. Ratchet effect: tests accumulate, mold gets more precise.
- Veo sources: `part3_mold_veo_01` → `part3_mold_veo_02` → `part3_mold_veo_03`
- Overlays:
  - Split: prompt vs code at ~0:21
  - Stat callout — CodeRabbit at ~0:25
  - Stat callout — DORA at ~0:40
- Camera: walls rising from ground, forming constraints around a central space; ratchet mechanism clicking into place
- Transition: crossfades between veo clips (20 frames)

### Act B — Prompt Capital (2:30–3:45)
- Narration: The prompt specifies what and why — not how. Implementation varies; behavior is locked. 1/5 to 1/10 the code size. Models trained on 30x more natural language. NL comments improved code generation 41%.
- Veo source: `part3_mold_veo_04` (prompt radiating)
- Overlay: Stat callout — NL context at ~3:27
- Camera: prompt text generates multiple valid implementations, radiating outward like light through a prism
- Transition: crossfade from Act A (20 frames)

### Act C — Grounding Capital (3:45–4:30)
- Narration: Learned from past generations — style, patterns, team conventions captured automatically. Feeds forward into future generations.
- Veo source: `part3_mold_veo_05` (grounding loop)
- Camera: cyclic visualization, learning from outputs, feeding back into a glowing loop
- Transition: crossfade from Act B (20 frames)

### Synthesis (4:30–4:40)
- Narration: Prompt + tests + grounding = intent + constraints + style = complete specification.
- Veo source: `part3_mold_veo_06` (three components merging)
- Camera: three colored streams (green, gold, purple) merge into a single glowing mold
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across acts
  - `veo/part3_mold_veo_01.mp4` (Title + Act A start)
  - `veo/part3_mold_veo_02.mp4` (Act A — ratchet)
  - `veo/part3_mold_veo_03.mp4` (Act A — Z3 proof)
  - `veo/part3_mold_veo_04.mp4` (Act B)
  - `veo/part3_mold_veo_05.mp4` (Act C)
  - `veo/part3_mold_veo_06.mp4` (Synthesis)
- Title card overlay (see `title_card.md`)
- Stat callout overlays synced to narration triggers (see stat_callout files)
- Split screen overlay (see `split_prompt_vs_code.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
