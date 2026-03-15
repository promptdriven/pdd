# Video Editor PDD

AI-first video editor webapp — the control plane for a full AI video production pipeline.

## Overview

A single Next.js webapp that orchestrates 10 pipeline stages from source script to finished video:

1. **Project Setup** — Initialize `project.json` with section registry, TTS and Veo config
2. **Script Editor** — Edit `narrative/main_script.md` with structured preview
3. **TTS Script Generation** — Claude Code extracts narration + adds `[TONE:]`/`[PACE:]`/`[PAUSE:]` annotations
4. **TTS Rendering** — Qwen3-TTS renders per-segment WAV files
5. **Audio Sync Pipeline** — `sync_audio_pipeline.py` concatenates, copies to `remotion/public/`, generates word timestamps
6. **Spec Generation** — Claude Code writes visual spec markdown files per section/segment
7. **Veo Generation** — Google Veo 3.1 generates video clips with frame chaining; Imagen 3.0 for character portraits
8. **Composition Generation** — Claude Code writes Remotion React components; asset staging to `remotion/public/`
9. **Render + Stitch** — Remotion renders sections in parallel; ffmpeg stitches full video
10. **Audit** — Parallel Claude Code agents compare rendered frames against specs

The Review tab provides the core annotation/fix loop:
- Spacebar pauses video and activates drawing canvas (1920×1080) + speech recognition
- Annotations accumulate per section; batch resolve triggers fix → render → stitch cycle
- All progress streamed via SSE

## Tech Stack

| Layer | Technology |
|-------|-----------|
| Web framework | Next.js 16.0.10 (App Router) |
| UI | React 19.2.3, Tailwind CSS 4.0.3 |
| Animation | Remotion 4.0.410 |
| Database | SQLite via `better-sqlite3` |
| AI (analysis + fixes) | Claude Opus 4.6 via CLI |
| Video generation | Google Veo 3.1 (`veo-3.1-generate-preview`) |
| Image generation | Google Imagen 3.0 (`imagen-3.0-generate-002`) |
| TTS | Qwen3-TTS 1.7B (local, `models/`) |
| Transcription | faster-whisper (Python subprocess) |
| Video processing | ffmpeg (system) |
| Script editor | CodeMirror 6 |
| Audio waveforms | WaveSurfer.js |
| Validation | Zod |

## Prerequisites

- Node.js 20+
- Conda or Miniforge for an isolated Python env
- Python 3.11+ with `faster-whisper` and `qwen_tts` installed
- ffmpeg in PATH
- `claude` CLI (`npm install -g @anthropic-ai/claude-code`)
- Google GenAI API key (for Veo + Imagen)
- Qwen3-TTS model weights in `models/` (~4.5GB)

## Setup

```bash
# 1. Create and activate the recommended Python env
conda create -n video_editor python=3.12 -y
conda activate video_editor

# Keep the env isolated from global/user Python packages.
# This avoids pulling in unrelated editable installs from the parent pdd repo.
conda env config vars set -n video_editor PYTHONNOUSERSITE=1 PYTHONPATH=
conda deactivate
conda activate video_editor

# 2. Install Node.js dependencies
npm install

# 3. Install Python dependencies
pip install -r requirements.txt

# If Qwen import fails with a huggingface-hub 1.x error, pin it back to the
# transformers-compatible range used by Stage 4:
pip install "huggingface-hub<1.0,>=0.34.0"

# 4. Download Qwen3-TTS model weights (first time only)
# See: https://huggingface.co/Qwen/Qwen3-TTS-1.7B
# Place under models/Qwen3-TTS-12Hz-1.7B-CustomVoice/ and models/Qwen3-TTS-Tokenizer-12Hz/

# 5. Set environment variables
cp .env.example .env.local
# Edit .env.local with your GOOGLE_API_KEY and paths
```

### Verify Stage 4 TTS

```bash
conda activate video_editor
python -c "import qwen_tts, torch; print({'qwen_tts': qwen_tts.__file__, 'cuda': torch.cuda.is_available(), 'mps': bool(getattr(getattr(torch, 'backends', None), 'mps', None) and torch.backends.mps.is_available())})"
```

Expected behavior:
- If `qwen_tts` imports successfully, Stage 4 uses local Qwen3-TTS.
- On Apple Silicon, Qwen should use `mps`.
- If Qwen import fails, Stage 4 falls back to `EdgeTTS`, which does not use the local GPU.

## Running Locally

```bash
conda activate video_editor
npm run dev
```

Open http://localhost:3000. Navigate to Stage 1 to initialize your project.

## Project Layout (after project init)

```
<project-root>/               # Your video project directory (set in Stage 1)
├── project.json              # Single source of truth for all pipeline config
├── narrative/
│   ├── main_script.md        # Human-written source script
│   └── tts_script.md         # Claude-generated TTS script (Stage 3 output)
├── specs/                    # Claude-generated visual specs (Stage 6 output)
│   └── {section}/
│       └── segment_NN_*.md
├── outputs/
│   ├── tts/                  # WAV segments + word timestamps (Stage 4-5 output)
│   │   └── {section}/
│   └── veo/                  # Raw + composited Veo clips (Stage 7 output)
│       └── {section}/
├── references/               # Imagen character portraits (Stage 7)
├── remotion/
│   ├── public/               # Staged assets (WAVs + MP4s) for Remotion
│   └── src/remotion/         # Remotion compositions (Stage 8 output)
└── audits/                   # Audit reports (Stage 10 output)
```

## Architecture

See `architecture.json` for the full module dependency graph.

Key design decisions:
- `project.json` is the single source of truth — hot-reloaded on save
- SQLite (`better-sqlite3`, sync API) for jobs and annotations
- SSE via `ReadableStream` in Next.js Route Handlers (not WebSockets)
- Tailwind v4 CSS-first config (`@theme {}` in `app/globals.css`, no `tailwind.config.js`)
- `better-sqlite3` in `next.config.ts` `serverExternalPackages`
- Remotion rendered via `@remotion/renderer` Node API (not CLI subprocess)
- Claude Code invoked via `child_process.spawn` with scoped `--allowedTools`
