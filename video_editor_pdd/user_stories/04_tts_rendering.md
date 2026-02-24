# User Story 04: TTS Audio Rendering

**As a** video director,
**I want to** render TTS audio from the generated script and preview individual segments,
**So that** I can hear the narration and re-render any segments that sound wrong before proceeding.

## Acceptance Criteria

- [ ] A table lists all TTS segments with columns: #, Segment ID, Status (not_started / running / done), and action buttons
- [ ] [Render All] renders every segment; [Render Missing] renders only segments without a `.wav` file
- [ ] Each row has a [Play] button that plays the segment's `.wav` inline via an `<audio>` element
- [ ] Each row has a [Re-render] button that regenerates just that segment
- [ ] Expanding a row shows a waveform preview and the raw TTS text for that segment
- [ ] A batch progress bar shows overall progress with the current segment ID
- [ ] Progress updates stream in real-time via SSE

## Mapping to PRD

- Section 4.6.5 (Stage 4: TTS Rendering)
- Section 5.2 (Audio Pipeline — TTS Renderer)
- Section 9.1 (Production Pipeline — TTS rendering)

## Technical Notes

- `POST /api/pipeline/tts-render/run` with `{ segments: [...] }` body
- TTS engine: Qwen3-TTS (local, 24kHz mono)
- Output: `outputs/tts/segment_NNN.wav`
- `done` = `.wav` file exists and is non-zero bytes
