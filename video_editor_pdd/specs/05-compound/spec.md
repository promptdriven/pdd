[Remotion] Part 5: Compound Returns

## Overview
- Composition ID: `Part5CompoundReturns`
- Duration: ~98.42s (1:38, matches narration audio)
- Remotion dir: `S05-CompoundReturns`
- Mood: momentum building → exponential growth realization

## Visual Design
- Background: Veo-generated conceptual visualizations with Remotion overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), test green (#22C55E), danger red (#EF4444), amber (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part5_compound/narration.wav`
- Word timestamps: `part5_compound/word_timestamps.json`
- Segments: `part5_compound_001` through `part5_compound_010`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "Compound Returns"
- `veo_01_maintenance_pie.md` — maintenance cost pie chart animation (10s)
- `veo_02_compound_debt_curve.md` — debt accumulation curves: patching vs generation (10s)
- `veo_03_diverging_trajectories.md` — patching and generation paths diverging over time (10s)
- `veo_04_grandmother_return.md` — callback to grandmother/darning metaphor (10s)
- `veo_05_quote_card.md` — quote card visualization (10s)
- `stat_callout_cisq.md` — CISQ stat: $2.41 trillion cost of poor software quality
- `stat_callout_maintenance.md` — maintenance cost stat: 80-90% of software cost
- `split_patching_vs_pdd.md` — split screen: patching approach vs PDD approach

## Narrative Arc & Shot Breakdown

### Title Card (0:00–0:05)
- Title card overlay: "Compound Returns"
- Veo source: `part5_compound_veo_01` (pie chart beginning)
- Overlay: title card with green accent
- Transition: fade-in from black (30 frames)

### Act A — Maintenance Burden (0:05–0:25)
- Narration: 80-90% of software cost is maintenance. Not features. Not launch. Maintenance. This is the elephant in the room.
- Veo source: `part5_compound_veo_01` (maintenance pie chart)
- Camera: pie chart animates in, maintenance slice dominates
- Overlay: stat callout — maintenance at ~0:18
- Transition: crossfade from title card

### Act B — Compound Debt (0:25–0:50)
- Narration: Patching accumulates debt linearly — each patch adds residual complexity. Generation resets debt each cycle — fresh code, no residue. The gap compounds.
- Veo source: `part5_compound_veo_02` (compound debt curves)
- Camera: dual curves drawing in — patching line climbs, generation line stays flat
- Overlay: stat callout — CISQ trillion at ~0:32
- Transition: crossfade from Act A (20 frames)

### Act C — Diverging Futures (0:50–1:15)
- Narration: Over months and years, the trajectories diverge dramatically. Teams that patch sink deeper. Teams that generate compound their advantage. Early adoption creates exponential separation.
- Veo source: `part5_compound_veo_03` (diverging trajectories)
- Camera: trajectories separate — one sinks, one rises
- Transition: crossfade from Act B (20 frames)

### Act D — Callback and Close (1:15–1:38)
- Narration: Your grandmother didn't need a study to figure this out. When the economics flip, you stop darning. You start buying new socks. We're at that moment for code.
- Veo sources: `part5_compound_veo_04` → `part5_compound_veo_05`
- Camera: grandmother metaphor callback, then quote card
- Overlays:
  - Split: patching vs PDD at ~1:25
- Transition: crossfade between veo_04 and veo_05 (20 frames), fade-out to black at end (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across acts
  - `veo/part5_compound_veo_01.mp4` (Title + Act A)
  - `veo/part5_compound_veo_02.mp4` (Act B)
  - `veo/part5_compound_veo_03.mp4` (Act C)
  - `veo/part5_compound_veo_04.mp4` (Act D start)
  - `veo/part5_compound_veo_05.mp4` (Act D end)
- Title card overlay (see `title_card.md`)
- Stat callout overlays synced to narration (see stat_callout files)
- Split screen overlay (see `split_patching_vs_pdd.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
