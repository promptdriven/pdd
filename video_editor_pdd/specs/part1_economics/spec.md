[Remotion] Part 1: The Economics of Code Generation

## Overview
- Composition ID: `Part1Economics`
- Duration: ~382.25s (6:22, matches narration audio)
- Remotion dir: `S01-Economics`
- Mood: analytical → ominous → optimistic

## Visual Design
- Background: Veo-generated cinematic infographic footage with Remotion data overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), circuit green (#22C55E), danger red (#EF4444), amber accent (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part1_economics/narration.wav`
- Word timestamps: `part1_economics/word_timestamps.json`
- Segments: `part1_economics_001` through `part1_economics_030`
- Silence gap: 0.3s default

## Visual Assets
- `veo_01_cost_graph.md` — animated dual-line cost graph showing patching vs generation crossover (10s)
- `veo_02_debt_accumulation.md` — technical debt accumulation visualization (10s)
- `veo_03_context_window.md` — context window degradation visualization (10s)
- `veo_04_regeneration.md` — code regeneration pipeline visualization (10s)
- `stat_callout_gitclear.md` — GitClear stat: churn up 44%, refactoring down 60%
- `stat_callout_github.md` — GitHub stat: 55% speedup, greenfield only
- `stat_callout_uplevel.md` — Uplevel stat: 800 devs, no throughput change, 41% more bugs
- `split_perception_vs_reality.md` — split screen: perceived speed vs actual outcomes

## Narrative Arc & Shot Breakdown

### Act A — Economics of Darning (0:00–1:30)
- Narration: Introduces the 1950s sock economy — cost of materials vs cost of labor. By the 1960s, the economics flipped. Socks became cheaper to replace than to repair.
- Veo source: `part1_economics_veo_01` (cost graph)
- Camera: animated graph drawing in, lines crossing
- Overlay: axis labels, data annotations animate in sequence

### Act B — AI Tools Validate the Premise (1:30–2:30)
- Narration: Cursor, Claude Code, Copilot — generation speed is real. These tools write code fast.
- Veo source: `part1_economics_veo_01` (continued, zoomed on generation line)
- Overlay: stat callout — GitHub 55% speedup appears at ~1:08

### Act C — The Hidden Cost (2:30–4:00)
- Narration: The dashed line — total cost — barely moves. GitHub study: 55% speedup but only greenfield. Uplevel: 800 devs, no throughput change, 41% more bugs. GitClear: 211M lines, churn up 44%, refactoring down 60%.
- Veo source: `part1_economics_veo_02` (debt accumulation)
- Overlays:
  - Stat callout — Uplevel at ~1:23
  - Stat callout — GitClear at ~1:55
- Camera: debt layers stacking up ominously

### Act D — Context Window Problem (4:00–5:15)
- Narration: Small codebase — AI is brilliant. Large codebase — performance degrades. EMNLP: 14-85% capability loss as context grows.
- Veo source: `part1_economics_veo_03` (context window degradation)
- Camera: visualization shrinks/distorts as window fills
- Overlay: capability percentage dropping

### Act E — Two Stories (5:15–5:45)
- Narration: Small codebases — AI transforms. Large codebases — devs are 19% slower but perceive 20% faster.
- Veo source: `part1_economics_veo_03` (continued)
- Overlay: split perception vs reality appears at ~4:15

### Act F — Regeneration Alternative (5:45–6:15)
- Narration: Prompts are 1/5 to 1/10 the size of code. MIT study: NL context improved code generation 89%. 250-line modules had lowest defect rates (U-curve).
- Veo source: `part1_economics_veo_04` (regeneration pipeline)
- Camera: compact prompt expands into full module, clean and fresh

### Act G — The Crossover (6:15–6:22)
- Narration: Generation cost has crossed below both lines. Debt resets. 80-90% of software cost is maintenance.
- Veo source: `part1_economics_veo_01` (return to cost graph, zoom on crossover)
- Camera: dramatic zoom to intersection point
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across acts
  - `veo/part1_economics_veo_01.mp4` (Acts A-B, return in G)
  - `veo/part1_economics_veo_02.mp4` (Act C)
  - `veo/part1_economics_veo_03.mp4` (Acts D-E)
  - `veo/part1_economics_veo_04.mp4` (Act F)
- Stat callout overlays synced to narration triggers (see stat_callout files)
- Split screen overlay (see `split_perception_vs_reality.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
