# Read the defect and review on both PRs

I can read the defect, detection gap, proof and review at the top of either PR, and a warning-light-only change keeps the issue open.

Person-reviewed source contract and expected cases approved by the root acting as the person under the flow lead's instructions. The prove and PR-evidence Runtime interfaces were approved through the actual CLI; the native-only runner integration received separate source review. Runtime check: not run; this Story's 13 steps and 32 checks remain unjudged (235 revised checks total). Native verification remains pending; the original 157-check baseline is historical evidence only.

## Acceptance criteria

1. Both PRs show accepted "Not fixed yet:", "Defect:", "Not caught because:", "Proof (defect fixed):", "Proof (gap closed):" and "Review:" lines in that order, with machine proof between the Proof lines and Review on the code PR; all lifted lines precede every replay status block.
2. Only authorized writers contribute: build/verify for "Not fixed yet:", bug reproduce or small-change scope for "Defect:" and "Not caught because:", verify for Proof, and the direct review note of an actual review step for "Review:". Summary review verdicts and missing-review-step verdicts are omitted; duplicate payloads differing only by one trailing period retain the first spelling.
3. Indented, case-varied, embedded and unknown-step labels and agent-written machine proof/inventory are not lifted; free-text payloads use control-safe adaptive code spans that neutralize @mentions, issue links and raw ownership-marker text.
4. When "Not fixed yet:" has a nonblank payload, both PRs use "Refs #2594"; otherwise PR 1 keeps "Part of #2594" and the code PR keeps "Closes #2594". Missing labels create no empty placeholders.
5. Both PRs show accepted "Not checked:" lines immediately after "Not fixed yet:" and before "Defect:", in latest summary then direct-note order for check, try, verify, formal, review and reproduce only; trim payload ends, preserve internal spaces and distinct lines, and deduplicate a single trailing period.
6. Indented, case-varied, embedded, unknown-step and unauthorized-writer "Not checked:" lines are omitted, and blank payloads create no placeholders on either PR.
7. A nonblank "Not checked:" line without a nonblank "Not fixed yet:" line keeps "Part of #2594" on PR 1 and "Closes #2594" on the code PR; with both labels, both PRs retain "Refs #2594".

## Rules to check

Column-zero exact labels only; trim payload ends, preserve distinct content, stable step/source order, duplicate removal ignoring one trailing period. Read latest saved summary then current direct note for each known step. A nonempty Not fixed yet line forbids runner-introduced closing references on both PRs. Reserve Tests vs base between machine proof and Review for integration; do not invent inventory.

## What must not change

The complete top evidence block precedes every replay status block; pending-before-push safeguards remain intact. Existing single ownership marker, Try-link removal, local-path redaction, report retention, 60000-code-point budget and publication-pending safeguards still apply to all added lines. Native create/update and body-protection tests must verify integration beyond this helper.
