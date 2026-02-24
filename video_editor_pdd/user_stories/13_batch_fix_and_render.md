# User Story 13: Batch Fix, Render, and Stitch

**As a** video director,
**I want to** review queued annotations for a section, preview proposed fixes, and apply them in a single batch that renders once,
**So that** multiple fixes are applied efficiently without redundant re-renders.

## Acceptance Criteria

- [ ] Annotations queue per section after analysis; user sees a count badge per section
- [ ] User can review each annotation's analysis, fixType badge, and suggested fixes
- [ ] Fix preview before execution: code diff for `remotion`, side-by-side clip preview for `veo`, audio playback comparison for `tts`
- [ ] User can accept, reject, or edit each fix in the queue before applying
- [ ] [Apply N Fixes] triggers a batch job that applies all accepted fixes sequentially, then renders the section once, then re-stitches the full video
- [ ] Per-annotation errors within a batch do not abort the batch; failed annotations are marked with error messages
- [ ] SSE streams per-annotation and overall progress
- [ ] Git auto-commits before and after Remotion fixes for rollback capability
- [ ] After completion, the video player reloads with the updated full video

## Mapping to PRD

- Section 4.4 (Job Management — per-section batch queue)
- Section 4.3 (Claude Integration — Fix)
- Section 9.2 (Review/Fix Loop — Batch fix trigger, Fix preview, AI fix, Section re-render)
- Section 9.3 (Reliability — Git integration)

## Technical Notes

- `POST /api/sections/:sectionId/resolve-batch` returns `{ jobId }` (HTTP 202)
- Fix routing by `fixType`: remotion -> Claude Code edit; veo -> Veo API regen; tts -> TTS re-render + audio sync
- Remotion fixes: Claude scoped to `remotion/src/remotion/{remotionDir}/` with `Read,Write,Edit,Glob,Grep`
- Render once per batch, not once per annotation
- Retry failed annotations via [Retry Failed] or re-queue in a new batch
