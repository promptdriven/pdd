[Remotion] Cold Open Section

## Overview
- Composition ID: `ColdOpenSection`
- Duration: ~15s (matches narration audio)
- Remotion dir: `S00-ColdOpen`
- Mood: conversational, knowing, building to gravitas

## Visual Design
- Background: Veo-generated cinematic footage of developer at desk
- Color palette: dark navy (#0A1628), monitor blue glow (#3B82F6), warm amber (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third
- Title card: "Why You're Still Darning Socks" fades in at start
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `cold_open/narration.wav`
- Word timestamps: `cold_open/word_timestamps.json`
- Segments: `cold_open_001` through `cold_open_006`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "Why You're Still Darning Socks"
- `veo_01_developer_desk.md` — wide shot, developer at multi-monitor desk (8s)
- `veo_02_developer_closeup.md` — close-up, reflective face + code in glasses (8s)

## Shot Breakdown

### Shot 1 — Hook (0:00–0:04)
- Narration: "If you use Cursor, or Claude Code, or Copilot... you're getting really good at this."
- Veo source: `cold_open_veo_01` (developer desk wide shot)
- Camera: slow dolly-in, shallow depth of field
- Overlay: title card fades in at frame 0, holds ~3s
- Transition: fade-in from black (30 frames)

### Shot 2 — Grandmother Insight (0:04–0:08)
- Narration: "But here's what your great-grandmother figured out sixty years ago."
- Veo source: `cold_open_veo_01` (continued) → crossfade to `cold_open_veo_02`
- Camera: hold, subtle push → transition to close-up
- Tone shift: reflective

### Shot 3 — The Punchline (0:08–0:10)
- Narration: "When socks got cheap enough... she stopped."
- Veo source: `cold_open_veo_02` (close-up)
- Pace: quicker delivery

### Shot 4 — The Thesis (0:10–0:12)
- Narration: "Code just got that cheap."
- Veo source: `cold_open_veo_02` (close-up, code reflecting in glasses)
- Pace: slow, each word lands

### Shot 5 — The Question (0:12–0:15)
- Narration: "So why are we still patching?"
- Veo source: `cold_open_veo_02` (hold on contemplative expression)
- Transition: fade-out to black (30 frames)

## Composition Structure
- Background layer: `veo/cold_open_veo_01.mp4` → crossfade → `veo/cold_open_veo_02.mp4`
- Crossfade point: ~4s mark (Shot 2 transition)
- Title card overlay with opacity interpolation (see `title_card.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
