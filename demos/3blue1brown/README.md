# 3Blue1Brown Demo — PDD Explainer Video

## Directory Structure

| Directory | Purpose |
|-----------|---------|
| `narrative/` | Video script and narration source (main_script.md, tts_script.md) |
| `specs/` | Visual segment specifications — one file per animated sequence, with per-spec AUDIT files |
| `remotion/` | Remotion + Next.js app — all React animation components and section compositions |
| `tools/` | Python scripts for TTS rendering (Qwen3 model) and Veo video generation |
| `outputs/` | All generated artifacts — section MP4s, TTS audio, Veo clips, frame extracts |
| `references/` | Research materials and source citations |
| `docs/` | Process documentation (rendering methodology, audio sync process) |
| `audits/` | QA audit reports — frame-by-frame visual verification |
| `models/` | Local Qwen3-TTS model weights |
| `archive/` | Stale files preserved for reference |

## Pipeline

```
narrative/*.md → tools/tts/*.py → outputs/tts/*.wav
                 tools/veo/*.py → outputs/veo/*.mp4
specs/*.md → remotion/src/remotion/*.tsx → outputs/sections/*.mp4 → outputs/full_video.mp4
```
