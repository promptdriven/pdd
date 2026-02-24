# User Story 21: Asset Staging Pipeline

**As a** director,
**I want** the app to automatically stage Veo clips and TTS audio to `remotion/public/` with manifest tracking,
**So that** Remotion compositions can find their required assets without manual file copying.

## Acceptance Criteria

- [ ] An asset manifest tracks all expected files in `remotion/public/` with their source paths (derived from specs and pipeline output)
- [ ] `GET /api/pipeline/asset-staging/manifest` returns the manifest with expected vs. present status for each file
- [ ] [Stage Now] button on individual missing files triggers `POST /api/pipeline/asset-staging/run` with `{ files: ["filename.mp4"] }`
- [ ] [Stage All Missing] button stages all files marked as missing in the manifest in a single job
- [ ] Staging copies files from `outputs/veo/` and `outputs/tts/` to `remotion/public/` with standardized filenames matching `staticFile()` references
- [ ] After Veo generation or TTS rendering completes, new assets are automatically staged (or flagged as needing staging)
- [ ] SSE streaming shows per-file staging progress
- [ ] Filename mapping follows the pattern: `outputs/veo/{section}/composited/{clip}.mp4` -> `remotion/public/{clip}.mp4`

## Mapping to PRD

- Section 5.3 Phase 3 (Asset Staging)
- Section 4.6.9 (Stage 8 — Asset Staging Manifest)
- Section 9.1 (Production Pipeline — Asset staging)
- Section 9.3 (Reliability — Asset manifest)
- Appendix A (`POST /api/pipeline/asset-staging/run`)

## Technical Notes

- The manifest is derived from spec files: `veo:filename` entries map to expected `staticFile("filename.mp4")` references
- TTS section WAVs are staged from `outputs/tts/{section}/{section}_narration.wav` to `remotion/public/{section}_narration.wav`
- Staging is a file copy operation, not a move — source files are preserved
- The manifest should detect stale files (source newer than staged copy) and mark them for re-staging
