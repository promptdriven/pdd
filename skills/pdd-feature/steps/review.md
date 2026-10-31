# review

You are the fresh independent reviewer; you neither built nor verified this change. Read only the issue, Story, `Defect:` block (including `Not caught because:`), diff against base, `Old-code proof:` and `Tests vs base:` evidence, PR 1 body and supplied step summaries. Do not open run-folder build.md, verify.md or formal.md; no builder notes, history or prior reviews. Inspect source, tests and the real changed path as needed.

Answer separately, one evidence-based line per question:
1. Is the defect fixed where it occurs and the detection gap closed? For new behavior, check its promise and coverage. A message or guard alone is not a defect fix.
2. Does every new test fail on old code for the bug's reason? Check the failing assertion and error; a crash, unrelated error or pass is not proof.
3. Compared with base, which tests were removed or assertions changed? Count and inspect; require a sound reason for each and preserve safety coverage. Matching output is not a reason.
4. Does coverage rely only on fake process, git, HTTP or files? Run one real changed path; compare the fake with the actual boundary, including termination and effects. Record command and outcome.
5. Is this only a warning light while the defect remains? Require `Not fixed yet: this helps find the cause` at the PR top, `Refs #N` rather than `Closes #N`, and keep the issue open.
6. Do claims in the PR 1 body, supplied step summaries and Story match the evidence, including failures, skips and unproved criteria?

Write `<run folder>/review.md`; first line: `Review: N must-fix` (unresolved count) or `Review: no must-fix`. Follow with six answers and findings: location, evidence, consequence, required correction. A must-fix is a problem build can fix in this change. Missing pdd-made `Old-code proof:` or `Tests vs base:` lines are limitations, not must-fixes. Other missing evidence is a limitation or finding, never a pass. Keep unresolved must-fixes visible after repair exhaustion; never turn exhaustion into a clean verdict. The skill owns repairs and the PR gate.

Merge only on the person’s explicit chat request under RUNBOOK §2: green current-head checks, safely quoted request comment first, then --merge --match-head-commit.
