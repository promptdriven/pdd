[Remotion] Part 5: Compound Returns

## Overview
- Composition ID: `Part5CompoundReturns`
- Duration: TBD (matches narration audio, ~2.25 minutes)
- Remotion dir: `S05-CompoundReturns`
- Segments: part5_compound_001 through part5_compound_010
- Mood: zooming out → mathematical weight → diverging futures → returning home → conviction

## Visual Design
- Primary: financial/mathematical visualizations — pie charts, compound curves, diverging trajectories
- Color palette: dark navy (#0F172A), alert red (#EF4444), test green (#22C55E), amber warning (#F59E0B), vibrant blue (#3B82F6), neutral gray (#94A3B8)
- Text overlay: rolling word-by-word narration subtitle at bottom third (12-word window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part5_compound/narration.wav`
- Word timestamps: `part5_compound/word_timestamps.json`
- Silence gap: 0.3s default

## Narrative Arc & Shot Map

### Act A — The Staggering Scale (0:00–0:25)
- "Now let's zoom out. Because the numbers you just saw — individual patches, individual bugs — add up to something staggering."
- 80–90% of software cost is maintenance, not building
- McKinsey: high tech debt → 40% more maintenance spend
- Stripe: devs waste 1/3 of work week on debt
- Visuals: pie chart morphing from initial dev vs maintenance, stat callouts
- Pacing: measured, factual, the weight of reality

### Act B — The Math of Accumulation (0:25–0:55)
- "And those costs compound — literally. Technical debt follows a compound interest curve."
- CISQ: $1.52 trillion annually in US technical debt
- "That's not a metaphor. It's the math of accumulation."
- Visuals: pie chart morphs into exponential debt curve, flat regeneration line appears
- Pacing: mathematical, precise, deliberate

### Act C — Two Trajectories (0:55–1:25)
- "Patching accrues compound costs. Each patch adds debt. Debt generates more debt."
- "But the mold works the other way. Each test constrains every future generation."
- "Tests accrue compound returns."
- Investment table: Fix a bug (one place vs impossible forever), Improve code (one version vs all future), Document intent (one snapshot vs living spec)
- Visuals: two diverging curves — patching exponential upward, PDD stays flat; investment comparison table
- Pacing: contrast, two futures becoming visible

### Act D — The Core Truth (1:25–1:40)
- "One side of this equation compounds against you. The other compounds for you."
- "That's not a marginal difference. Over time, it's everything."
- Visuals: the gap between curves widens dramatically, pulsing emphasis
- Pacing: slower, distilled, each word landing

### Act E — Returning Home (1:40–2:00)
- "Your great-grandmother wasn't stupid for darning socks. The economics made it rational."
- "And you're not stupid for patching code. Until now, the economics made it rational."
- "But the economics changed. And when economics change, behavior that was rational becomes... darning socks."
- Visuals: return to grandmother/socks motif, return to developer with Cursor, economics crossing point pulses
- Pacing: warm, respectful, then the turn — deliberate, inevitable

### Act F — The Contrarian Bet (2:00–2:15)
- "A researcher at Microsoft, after seeing PDD for the first time, said: 'This is either the way of the future or it's going to crash and burn spectacularly.'"
- "He's right — it's a contrarian bet. But the economics are on our side."
- Visuals: clean quote card with typography, then fade
- Pacing: lighter, wry amusement, confidence

## Composition Structure
- Full-screen Veo backgrounds transitioned by act
- Animated subtitle track synced to word timestamps (12-word rolling window)
- Compound curves as key persistent overlay during Acts B–D
- Investment comparison table overlay during Act C
- Statistic callouts as animated overlays synced to narration timestamps
- Fade-in/fade-out transitions (30 frames each)
