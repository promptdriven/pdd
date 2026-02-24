# User Story 18: Fix Preview Before Execution

**As a** director,
**I want to** preview what Claude will change before applying a fix,
**So that** I can accept, reject, or edit each proposed fix before it modifies my project.

## Acceptance Criteria

- [ ] For `remotion` fixes: show a code diff (red/green unified diff) of the proposed .tsx file changes
- [ ] For `veo` fixes: show a side-by-side clip preview (current clip vs. regenerated clip)
- [ ] For `tts` fixes: show an audio playback comparison (current segment vs. re-rendered segment)
- [ ] Each fix in a batch can be individually accepted, rejected, or edited before the batch executes
- [ ] Rejected fixes are removed from the batch without affecting other fixes
- [ ] Edited fixes update the proposed changes before execution
- [ ] [Apply N Fixes] button updates its count as fixes are accepted/rejected
- [ ] Preview generation does not modify any project files — changes are applied only on explicit confirmation

## Mapping to PRD

- Section 9.2 (Review/Fix Loop — Fix preview per fix type)
- Section 10 (Known Limitations — No undo beyond git; diff preview is essential)

## Technical Notes

- Remotion diff preview: Claude generates the fix in a dry-run mode, returns proposed file edits as a diff
- Veo preview: server generates the clip to a temp location, streams preview without overwriting the original
- TTS preview: server renders the segment to a temp file for A/B playback
- Diff rendering can use a library like `react-diff-viewer` or the existing `diff` package used in Stage 3
