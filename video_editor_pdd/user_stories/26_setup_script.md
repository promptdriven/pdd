# User Story 26: Setup Script and Dependency Management

**As a** developer setting up the project for the first time,
**I want** a single `make setup` command that installs all dependencies and prepares the environment,
**So that** first-time setup is reliable and doesn't require reading scattered documentation.

## Acceptance Criteria

- [ ] `make setup` (or `./setup.sh`) installs all Python dependencies from `requirements.txt`
- [ ] `make setup` installs all Node dependencies via `npm install`
- [ ] `make setup` downloads Qwen3-TTS model weights (~4.5GB) to `models/` if not already present
- [ ] `make setup` verifies `ffmpeg` is installed and accessible on PATH; prints a clear error if missing
- [ ] `make setup` creates required directories: `outputs/`, `references/`, `audits/`, `data/`, `models/`
- [ ] `make setup` initializes the SQLite database with required tables
- [ ] `requirements.txt` includes all Python dependencies: `qwen_tts`, `google-genai`, `faster-whisper`, `soundfile`, `transformers`
- [ ] Running `make setup` a second time is idempotent (skips already-completed steps)
- [ ] Setup prints a summary of what was installed and any manual steps remaining (e.g., Google Cloud API key configuration)

## Mapping to PRD

- Section 9.3 (Reliability — Setup script, Dependency management)
- Section 6 (Tech Stack — Python Tools, Model Setup)

## Technical Notes

- Model download: HuggingFace Hub CLI or direct HTTP download from model repository
- Model paths: `models/Qwen3-TTS-12Hz-1.7B-CustomVoice/` (3.8GB) and `models/Qwen3-TTS-Tokenizer-12Hz/` (682MB)
- ffmpeg check: `which ffmpeg` or `ffmpeg -version`
- SQLite init: run migrations from `lib/db.ts` schema
