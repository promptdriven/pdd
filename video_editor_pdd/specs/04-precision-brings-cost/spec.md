[Remotion] Part 4: The Precision Tradeoff

## Overview
- Composition ID: `Part4PrecisionTradeoff`
- Duration: TBD (matches narration audio, ~2.5 minutes)
- Remotion dir: `S04-PrecisionTradeoff`
- Segments: part4_precision_001 through part4_precision_011
- Mood: curious exploration → satisfying insight → pragmatic balance

## Visual Design
- Primary: manufacturing comparison (3D printing vs injection molding), then abstract curves and spectrums
- Color palette: dark navy (#0F172A), test green (#22C55E), prompt gold (#F59E0B), verification blue (#3B82F6), neutral gray (#94A3B8)
- Text overlay: rolling word-by-word narration subtitle at bottom third
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `part4_precision/narration.wav`
- Word timestamps: `part4_precision/word_timestamps.json`
- Silence gap: 0.3s default

## Narrative Arc & Shot Map

### Act A — The Two Kinds of Precision (0:00–0:30)
- "Let's talk about precision. Because there's a subtle tradeoff that changes how you think about prompts."
- 3D printing: every point must be specified, no mold, extreme precision required
- Injection molding: walls do the precision work, material just flows
- Visuals: split-screen 3D printer vs injection mold, coordinate grid overlay
- Pacing: curious, exploratory

### Act B — The Inverse Curve (0:30–1:15)
- "This maps directly to PDD."
- Few tests → prompt must specify everything (edge cases, error handling, exact behavior)
- Many tests → prompt only needs intent, tests handle constraints
- Graph: X = number of tests, Y = required prompt precision, inverse curve
- Visuals: animated graph with slider moving along the curve, prompt shrinking as tests grow

### Act C — Why Test Accumulation Matters (1:15–1:45)
- "This is why test accumulation matters. It's not just about catching bugs."
- Making prompts simpler and regeneration safer over time
- "The more walls you have, the less you need to specify. The mold does the precision work."
- Visuals: dense prompt (50 lines) → minimal prompt (10 lines) with 47 tests surrounding it

### Act D — When Code-Level Precision Is Needed (1:45–2:15)
- "But some things genuinely need code-level precision."
- Algorithm choice, performance-critical inner loops, bit-level operations
- Prompt can embed code snippets for critical sections
- "Stay in prompt space as long as possible — then dip into code when the precision demands it."
- Visuals: prompt document with embedded code block, fluid boundary

### Act E — The Spectrum (2:15–2:30)
- "Think of it as a spectrum. Natural language on one end, code on the other."
- "The question isn't 'prompts OR code.' It's 'how far into prompt space can you stay?'"
- "For most of the specification — further than you'd think."
- Visuals: gradient slider from blue (NL) to gray (code), positioned mostly left

## Composition Structure
- Full-screen Veo backgrounds transitioned by act
- Animated subtitle track synced to word timestamps
- Precision curve diagram as key persistent overlay during Acts B–C
- Spectrum slider as closing visual motif
- Fade-in/fade-out transitions (30 frames each)
