[Remotion] Animation Section

## Overview
- Composition ID: `AnimationSection`
- Duration: ~20s (matches narration audio)
- Remotion dir: `S00-AnimationSection`
- Mood: energetic, demonstrative, technical clarity

## Visual Design
- Background: Veo-generated abstract motion footage with Remotion overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), circuit green (#22C55E), amber accent (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Title card: "Animation Pipeline Demo" fades in at start
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `animation_section/narration.wav`
- Word timestamps: `animation_section/word_timestamps.json`
- Segments: `animation_section_001` through `animation_section_002`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "Animation Pipeline Demo"
- `veo_01_abstract_motion.md` — abstract geometric animation background (10s)
- `stat_callout_demo.md` — statistic overlay demonstrating callout rendering

## Shot Breakdown

### Shot 1 — Introduction (0:00–0:06)
- Narration: "Remotion compositions layer animated overlays on top of AI-generated video."
- Veo source: `animation_section_veo_01` (abstract motion)
- Camera: slow zoom-in on geometric shapes forming
- Overlay: title card fades in at frame 0, holds ~3s
- Transition: fade-in from black (30 frames)

### Shot 2 — Overlay Demo (0:06–0:14)
- Narration: "Each layer — titles, statistics, subtitles — renders in sync with the narration timeline."
- Veo source: `animation_section_veo_01` (continued)
- Overlays: stat callout appears at ~7s, demonstrating animated data overlay
- Transition: crossfade between overlay states

### Shot 3 — Closing (0:14–0:20)
- Narration: "This pipeline transforms specs into polished video segments automatically."
- Veo source: `animation_section_veo_01` (hold on final frame)
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: `veo/animation_section_veo_01.mp4`
- Title card overlay with opacity interpolation (see `title_card.md`)
- Stat callout overlay synced to narration (see `stat_callout_demo.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
