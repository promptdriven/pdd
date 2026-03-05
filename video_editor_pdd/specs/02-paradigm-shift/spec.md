[Remotion] Part 2: The Paradigm Shift

## Overview
- Composition ID: `Part2ParadigmShift`
- Duration: ~195.79s (3:15, matches narration audio)
- Remotion dir: `S02-ParadigmShift`
- Mood: expansive wonder → concrete illustration → conviction

## Visual Design
- Background: Veo-generated cinematic footage of manufacturing and chip design
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), molten orange (#F97316), circuit green (#22C55E), steel gray (#64748B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part2_paradigm_shift/narration.wav`
- Word timestamps: `part2_paradigm_shift/word_timestamps.json`
- Segments: `part2_paradigm_shift_001` through `part2_paradigm_shift_019`
- Silence gap: 0.3s default

## Visual Assets
- `01_injection_molding.md` — injection molding process animation (10s)
- `02_value_migration.md` — value migrating from object to specification (10s)
- `03_chip_design.md` — 1980s hand-drawn gates to HDL transition (10s)
- `04_prompt_is_mold.md` — prompt-to-code generation flow visualization (10s)

## Narrative Arc & Shot Breakdown

### Act A — Pattern Across Industries (0:00–0:45)
- Narration: Not cheaper materials — a shift in how things are made. The same pattern across textiles, plastics, semiconductors. The value didn't stay in the thing itself.
- Veo source: `part2_paradigm_shift_veo_01` (injection molding)
- Camera: macro view of molten material flowing into a precision mold
- Overlay: none (subtitles only)
- Transition: fade-in from black (30 frames)

### Act B — Injection Molding Metaphor (0:45–1:30)
- Narration: Design the mold once, produce unlimited identical parts. Find a defect? Fix the mold — not every individual part. The cost is in the specification, not the production.
- Veo source: `part2_paradigm_shift_veo_01` (continued — mold producing parts)
- Camera: pull back to reveal production line of identical parts emerging
- Overlay: none (subtitles only)

### Act C — Value Migration (1:30–2:00)
- Narration: Value migrates from the object to the specification. The plastic part is disposable. The mold is everything.
- Veo source: `part2_paradigm_shift_veo_02` (value migration diagram)
- Camera: abstract visualization — value flowing from physical object upward to blueprint
- Transition: crossfade from Act B (20 frames)

### Act D — Chip Design History (2:00–2:45)
- Narration: 1980s — engineers hand-drew gate layouts. 1985 — Verilog HDL: describe behavior, not wires. Synopsys added verification with SAT and SMT solvers. Same revolution: specification replaced manual construction.
- Veo source: `part2_paradigm_shift_veo_03` (chip design transition)
- Camera: morphing from hand-drawn schematic to HDL text to automated layout
- Transition: crossfade from Act C (20 frames)

### Act E — The Connection (2:45–3:15)
- Narration: "The prompt is your mold. Code is plastic. Tests lock the behavior. We've seen this before — we just didn't recognize it."
- Veo source: `part2_paradigm_shift_veo_04` (prompt-to-code flow)
- Camera: prompt text transforms into flowing code, test barriers appear on edges
- Transition: crossfade from Act D, fade-out to black at end (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across acts
  - `veo/part2_paradigm_shift_veo_01.mp4` (Acts A-B)
  - `veo/part2_paradigm_shift_veo_02.mp4` (Act C)
  - `veo/part2_paradigm_shift_veo_03.mp4` (Act D)
  - `veo/part2_paradigm_shift_veo_04.mp4` (Act E)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
