# Import saved evidence from an authorized workspace

I can record my saved check from an authorized clone or bounded workspace while my run continues, including a PR 1 check after code work starts.

Draft for review. The authorization route, metadata and frozen-source choice below are proposed. No workspace has been authorized by this draft.

## Acceptance criteria

1. An explicitly authorized clean clone with the complete matching selected source can import its original saved JSON; an authorized nested bounded workspace can do the same.
2. A same-source clone or nested repository without authorization is refused; equal content, a shared remote and nesting do not grant permission.
3. An association for another run, another repository owner or another producer root is refused without a saved evidence change.
4. A missing, changed, extra or stale selected source file, including a required Story or prompt dependency, is refused even when the test file is unchanged.
5. After code work starts, original PR 1 evidence can import against its explicitly authorized frozen PR 1 source; a missing or wrong PR 1 anchor is refused and current code cannot replace it.
6. Imports preserve the original JSON and all result provenance, leave workflow progress and publication unchanged, and retain stage identity in later status and PR evidence selection; repeated imports need no new check.

## Rules to check

Permission and source equality are separate requirements. Refuse any alternate producer unless a person-reviewed association binds that exact root to the owned run, repository owner and evidence stage. A receipt must never authorize itself. The forbidden result is acceptance based only on equal content, a shared remote, a shared commit or a nested path.

Compare the entire selected source with the reviewed stage source. A PR 1 result must never become a current-code result. Refusals save nothing. Import does not approve a gate, execute a check or publish a PR.

## Proposed person choices

Use a separate `evidence-associate` route with the existing person-approval policy. Store its authorization outside the receipt. Bind PR 1 to the owned run's recorded PR 1 head, with a locally retained frozen source and exact test selection. Keep ordinary same-worktree behavior.

## Cases and proof limit

The scenario and native case draft call the real saved-evidence boundary. They derive expected outcomes from this request, not from implementation output. The current Runtime interface has no honest ingestion binding; no Interpreter pass or failure is claimed. Native filesystem, ownership, capture, persistence and later status/PR effects still require execution against implementation after approval.
