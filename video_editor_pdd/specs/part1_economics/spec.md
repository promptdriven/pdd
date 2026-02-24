[Remotion] Part 1: The Economics of Darning

## Overview
- Composition ID: `Part1Economics`
- Duration: ~382s (matches narration audio)
- Remotion dir: `S01-Economics`
- Segments: `part1_economics_001` through `part1_economics_030`
- Mood: analytical → ominous → optimistic

## Visual Design
- Primary background: animated data visualizations (3Blue1Brown-inspired)
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), amber warning (#F59E0B), red alert (#EF4444), green positive (#22C55E)
- Text overlay: rolling word-by-word narration subtitle at bottom third (12-word window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part1_economics/narration.wav`
- Word timestamps: `part1_economics/word_timestamps.json`
- Silence gap: 0.3s default

## Narrative Arc & Shot Map

### Act A — The Darning Analogy (0:00–1:30)
- "This isn't nostalgia. It's economics."
- Sock cost vs labor in 1950 → math flip in 1960s
- Parallel to code: writing from scratch was expensive, patching was rational
- Visuals: animated line charts, cost comparison infographic

### Act B — AI Makes Patching Faster (1:30–2:30)
- AI tools validate: Cursor, Claude Code, Copilot are incredible
- "Each patch is getting faster. That's real."
- Visuals: speedometer animation, individual task timers shrinking

### Act C — The Hidden Cost (2:30–4:00)
- "Watch the dashed line. The total cost. It's barely moving."
- Residue = technical debt, accumulates faster with faster patching
- GitHub 55% speedup stat → but greenfield only
- Uplevel: 800 devs, no throughput change, 41% more bugs
- GitClear: 211M lines, churn up 44%, refactoring down 60%
- Visuals: dual-axis chart with per-patch cost vs total cost, statistics callouts

### Act D — Context Window Problem (4:00–5:15)
- Small codebase → AI brilliant, context covers everything
- Large codebase → window stays same, AI must guess
- Embedding search vs agentic search tradeoffs
- EMNLP study: 14–85% degradation from input length ("context rot")
- Visuals: expanding codebase diagram vs fixed window, retrieval accuracy chart

### Act E — Two Stories (5:15–5:45)
- Small codebase: patching with AI is transformative
- Large codebase: devs 19% slower, believed 20% faster (39pt gap)
- "Patching pushes you from the world where AI helps into the world where it doesn't"
- Visuals: split screen comparison, perception vs reality gauge

### Act F — Regeneration Alternative (5:45–6:15)
- Prompt = 1/5 to 1/10 size of code
- Natural language: models trained on 30x more NL than code
- MIT: NL context improved performance up to 89%
- 250-line modules have lowest defect density (U-curve)
- Visuals: prompt-to-code size comparison, U-shaped defect curve

### Act G — The Crossover (6:15–6:30)
- Generation cost crossed below both lines
- Debt resets with each regeneration
- "Best darning needles ever made... but still darning needles"
- 80–90% of software cost is maintenance, not building
- Visuals: crossover chart with three lines, maintenance cost pie chart

## Composition Structure
- Full-screen Veo background video (`veo/part1_economics.mp4`) looped if shorter
- Animated subtitle track synced to word timestamps (12-word rolling window)
- Fade-in/fade-out transitions (30 frames each)
- Statistic callouts as animated overlays synced to narration timestamps
