# Read the defect and review on both PRs

I can read the defect, detection gap, proof and review at the top of either PR, and a warning-light-only change keeps the issue open.

Draft for person review; these proposed policies and expected values are not approved.

## Acceptance criteria

1. Both PRs show nonblank "Not fixed yet:", "Defect:", "Not caught because:", "Proof (defect fixed):", "Proof (gap closed):" and "Review:" lines in that order, with machine proof between the Proof lines and Review on the code PR.
2. Distinct lines from the latest known-step summaries and direct notes are retained in workflow step order within each label; exact repeats and blank labels are omitted.
3. Indented labels, different case, labels inside other text, unknown-step notes and agent-written machine proof or inventory lines are not lifted.
4. When "Not fixed yet:" has a nonblank payload, both PRs use "Refs #2594"; otherwise PR 1 keeps "Part of #2594" and the code PR keeps "Closes #2594". Missing labels create no empty placeholders.

## Rules to check

Column-zero exact labels only; trim payload ends, preserve distinct content, stable step/source order, exact duplicate removal. Read latest saved summary then current direct note for each known step. A nonempty Not fixed yet line forbids runner-introduced closing references on both PRs. Reserve Tests vs base between machine proof and Review for integration; do not invent inventory.

## What must not change

Replay/vector failure warnings retain precedence. Existing single ownership marker, Try-link removal, local-path redaction, report retention, 60000-code-point budget and publication-pending safeguards still apply to all added lines. Native create/update and body-protection tests must verify integration beyond this helper.
