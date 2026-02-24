# User Story 03: TTS Script Generation

**As a** video director,
**I want to** trigger Claude Code to generate a TTS-optimized script from my source script,
**So that** I get narration text with proper pacing annotations (`[TONE:]`, `[PACE:]`, `[PAUSE:]`) ready for audio rendering.

## Acceptance Criteria

- [ ] Clicking [Generate TTS Script] invokes Claude Code server-side to produce `tts_script.md`
- [ ] A progress log streams in real-time via SSE showing Claude's activity
- [ ] A unified diff view shows the source vs. generated script (red = removed, green = added)
- [ ] An inline CodeMirror editor below the diff allows post-generation manual edits to `tts_script.md`
- [ ] Manual edits auto-save on blur / 1-second debounce
- [ ] [Render Audio] button is enabled once `tts_script.md` exists on disk
- [ ] Re-running generation overwrites the previous TTS script (with a confirmation if edits exist)

## Mapping to PRD

- Section 4.6.4 (Stage 3: TTS Script Generation)
- Section 5.2 (Audio Pipeline — script extraction)
- Section 9.1 (Production Pipeline — Script to TTS script generation)

## Technical Notes

- `POST /api/pipeline/tts-script/run` triggers the job, returns `{ jobId }`
- SSE via `GET /api/jobs/:id/stream`
- Claude extracts narration, strips visual descriptions, adds TTS annotations and emphasis markers
