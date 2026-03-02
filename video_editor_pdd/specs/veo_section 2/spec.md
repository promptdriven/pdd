[Remotion] Veo Section

## Overview
- Composition ID: `VeoSection`
- Duration: ~25s (matches narration audio)
- Remotion dir: `S01-VeoSection`
- Mood: cinematic, immersive, contemplative to resolute

## Visual Design
- Background: Veo-generated cinematic footage with crossfade transitions
- Color palette: dark navy (#0A1628), cool blue (#3B82F6), steel gray (#64748B), warm amber (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `veo_section/narration.wav`
- Word timestamps: `veo_section/word_timestamps.json`
- Segments: `veo_section_001` through `veo_section_002`
- Silence gap: 0.3s default

## Visual Assets
- `veo_01_cinematic_landscape.md` — wide establishing shot, futuristic cityscape at dusk (8s)
- `veo_02_technology_closeup.md` — close-up, circuit boards and data streams (8s)
- `split_before_after.md` — split-screen: traditional workflow vs AI-assisted workflow

## Shot Breakdown

### Shot 1 — Establishing (0:00–0:08)
- Narration: "Veo generates cinematic footage from text descriptions, turning written specs into visual reality."
- Veo source: `veo_section_veo_01` (cityscape wide shot)
- Camera: slow aerial dolly over cityscape at golden hour
- Transition: fade-in from black (30 frames)

### Shot 2 — The Detail (0:08–0:16)
- Narration: "Each clip is precision-crafted: lighting, motion, and composition controlled by the prompt."
- Veo source: `veo_section_veo_01` → crossfade → `veo_section_veo_02`
- Camera: macro pull-back revealing circuit landscape
- Overlay: split-screen comparison appears at ~12s

### Shot 3 — Resolution (0:16–0:25)
- Narration: "From spec to screen — the pipeline stitches AI-generated footage into a cohesive narrative."
- Veo source: `veo_section_veo_02` (continued)
- Camera: hold on data streams coalescing
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: `veo/veo_section_veo_01.mp4` → crossfade → `veo/veo_section_veo_02.mp4`
- Crossfade point: ~10s mark (Shot 2 transition)
- Split-screen overlay synced to narration (see `split_before_after.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
