[Remotion] Cold Open — Why You're Still Darning Socks

## Overview
- Composition ID: `ColdOpenSection`
- Duration: ~15.68s (matches narration audio)
- Remotion dir: `S00-ColdOpen`
- Mood: conversational, knowing, building to gravitas

## Visual Design
- Background: Veo-generated cinematic developer footage with Remotion overlays
- Color palette: dark navy (#0F172A), vibrant blue (#3B82F6), cool monitor glow (#60A5FA), amber accent (#F59E0B)
- Text overlay: word-by-word narration subtitle at bottom third (12-word rolling window)
- Title card: "Why You're Still Darning Socks" fades in at start
- Typography: sans-serif, 36px subtitles with semi-transparent black backdrop

## Audio
- Narration: `cold_open/narration.wav`
- Word timestamps: `cold_open/word_timestamps.json`
- Segments: `cold_open_001` through `cold_open_006`
- Silence gap: 0.3s default

## Visual Assets
- `title_card.md` — title overlay: "Why You're Still Darning Socks"
- `veo_01_developer_desk.md` — wide shot of developer at multi-monitor desk (8s)
- `veo_02_developer_closeup.md` — close-up of developer face with code reflected in glasses (8s)

## Narrative Arc & Shot Breakdown

### Shot 1 — The Hook (0:00–0:08)
- Narration: "If you use Cursor, Claude Code, or Copilot — you're getting really good at this. Your grandmother figured out socks got cheap, and she stopped darning."
- Veo source: `cold_open_veo_01` (developer desk wide shot)
- Camera: slow dolly-in toward developer at multi-monitor workstation
- Overlay: title card fades in at frame 0, holds ~4s
- Transition: fade-in from black (30 frames)

### Shot 2 — The Thesis (0:08–0:15.68)
- Narration: "Code just got that cheap. So why are we still patching?"
- Veo source: `cold_open_veo_02` (developer close-up)
- Camera: close-up, code reflecting in glasses, contemplative expression
- Overlay: none (subtitles only)
- Transition: crossfade from shot 1 (20 frames), fade-out to black at end (30 frames)

## Composition Structure
- Background layer: `veo/cold_open_veo_01.mp4` → crossfade → `veo/cold_open_veo_02.mp4`
- Title card overlay with opacity interpolation (see `title_card.md`)
- Animated subtitle track synced to word timestamps
- Fade-in from black: 30 frames at start
- Fade-out to black: 30 frames at end
