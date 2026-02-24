# User Story 19: Git Integration for Remotion Fixes

**As a** director,
**I want** Claude fixes to be auto-committed to git before and after changes,
**So that** I can view diffs of what changed and revert bad fixes.

## Acceptance Criteria

- [ ] Before applying a batch of Remotion fixes, the server auto-commits all current changes with message "pre-fix: {sectionId} batch {batchId}"
- [ ] After each successful Remotion fix, the server auto-commits the modified files with message "fix: {annotationId} — {summary}"
- [ ] The annotation detail panel shows a [View Diff] button that displays the git diff for that fix's commit
- [ ] A [Revert Fix] button runs `git revert` on the fix's commit and triggers a re-render of the section
- [ ] Git operations are scoped to `remotion/src/remotion/{remotionDir}/` — no commits touch files outside the fix scope
- [ ] If git is not initialized or unavailable, fixes still work but a warning banner shows "Git integration unavailable — no rollback support"

## Mapping to PRD

- Section 9.2 (Review/Fix Loop — git commit per batch for rollback)
- Section 9.3 (Reliability — Git integration)
- Section 10 (Known Limitations — No undo beyond git)

## Technical Notes

- Git operations use `child_process.execSync` or a git library (e.g., `simple-git`)
- Commits are local only — no push to remote
- Veo and TTS fixes produce binary files; git tracks them but diffs are not meaningful — the UI should show "Binary file changed" for those fix types
- Revert creates a new commit (not `reset --hard`) to preserve history
