[Remotion] Closing — The Future of Code

## Overview
- Composition ID: `ClosingSection`
- Duration: ~21.07s (0:21, matches narration audio)
- Remotion dir: `S06-Closing`
- Mood: resolution, conviction, call to action

## Visual Design
- Background: Veo-generated cinematic footage with Remotion overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), test green (#22C55E), amber (#F59E0B), white (#FFFFFF)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `closing/narration.wav`
- Word timestamps: `closing/word_timestamps.json`
- Segments: `closing_001` through `closing_006`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — closing title overlay
- `veo_01_economics_flip.md` — economics curves flipping visualization (5s)
- `veo_02_mold_assembly.md` — complete mold assembly visualization (5s)
- `veo_03_developer_closes_laptop.md` — developer closes laptop, callback to opening (5s)
- `veo_04_cta_card.md` — call-to-action card (6s)
- `stat_callout_roi.md` — ROI stat for PDD adoption
- `split_darning_vs_molding.md` — split screen: darning vs molding economics

## Narrative Arc & Shot Breakdown

### Shot 1 — Resolution (0:00–0:07)
- Narration: "The economics have flipped. Patching is the old way — expensive, fragile, compounding."
- Veo source: `closing_veo_01` (economics flip)
- Overlay:
  - Title card at frame 0
  - Stat callout — ROI at 0:00
- Transition: fade-in from black (30 frames)

### Shot 2 — The Mold (0:07–0:12)
- Narration: "Design your mold — prompt, tests, grounding — and let generation do the rest."
- Veo source: `closing_veo_02` (mold assembly)
- Camera: three-component mold assembling into position

### Shot 3 — Callback (0:12–0:17)
- Narration: "Stop darning. Start molding."
- Veo source: `closing_veo_03` (developer closes laptop)
- Overlay: split darning vs molding at ~0:18
- Camera: developer closing laptop with satisfied expression, callback to cold open

### Shot 4 — CTA (0:17–0:21)
- Narration: silence / music swell
- Veo source: `closing_veo_04` (CTA card)
- Camera: clean CTA card with project branding
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: Veo videos crossfade across shots
  - `veo/closing_veo_01.mp4` (Shot 1)
  - `veo/closing_veo_02.mp4` (Shot 2)
  - `veo/closing_veo_03.mp4` (Shot 3)
  - `veo/closing_veo_04.mp4` (Shot 4)
- Title card overlay (see `title_card.md`)
- Stat callout overlay (see `stat_callout_roi.md`)
- Split screen overlay (see `split_darning_vs_molding.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
