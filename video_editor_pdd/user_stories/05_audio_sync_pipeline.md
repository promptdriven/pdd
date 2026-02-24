# User Story 05: Audio Sync Pipeline

**As a** video director,
**I want to** group TTS segments into sections, concatenate them with silence gaps, and run Whisper transcription,
**So that** I get word-level timestamps that drive all animation timing downstream.

## Acceptance Criteria

- [ ] A section grouping table maps segment ID ranges to section IDs (inline-editable)
- [ ] [Save Config] persists grouping to `project.json` under `audioSync.sectionGroups`
- [ ] [Run Audio Sync] triggers `sync_audio_pipeline.py` with SSE progress streaming
- [ ] Pipeline concatenates segments with `[PAUSE: Xs]` silence gaps, copies section WAVs to `remotion/public/`
- [ ] Pipeline runs Whisper transcription producing per-section `word_timestamps.json`
- [ ] A word timestamp viewer table shows: Word, Start (seconds), End (seconds), Segment ID
- [ ] The word table supports filtering by section and searching by word
- [ ] Virtual scrolling handles large scripts without UI lag

## Mapping to PRD

- Section 4.6.6 (Stage 5: Audio Sync Pipeline)
- Section 5.2 (Audio Pipeline — sync pipeline, Whisper, composition generator)
- Section 8.4 (Audio is Source of Truth)

## Technical Notes

- `POST /api/pipeline/audio-sync/run`
- Audio is the source of truth for all downstream timing — never estimate from script text
- Silence gaps use `np.zeros` at sample rate, not ffmpeg
- Whisper output feeds into `generate_section_compositions.py` to produce BEATS constants
