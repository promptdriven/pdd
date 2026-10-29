# review

Use a fresh independent subagent that neither built nor verified this change. Give it only the issue, Story, `Defect:` block (including `Not caught because:`), diff against base, `Old-code proof:` and `Tests vs base:` evidence. Never give builder notes, previous reviews or chat history. Inspect source, tests and the real changed path as needed. For the claims check, inspect only Story, PR-body and status claims, excluding embedded step notes.

Answer each question separately, one evidence-based line per question:
1. Is the defect fixed where it occurs and the detection gap closed? For new behavior, check the promised behavior and its coverage. A message or guard alone is not evidence of a defect fix.
2. Does every new test fail on old code for the bug's reason? Check the actual failing assertion and error; a crash, unrelated error or pass on old code is not proof.
3. Compared with base, which tests were removed or assertions changed? Count and inspect them; require a sound reason for each and preserve their safety coverage. Matching current output is not a reason.
4. Does changed-code coverage rely only on fake process, git, HTTP or files? Run one real changed path and compare the fake's behavior with the actual boundary, including termination and effects. Record the command and outcome.
5. Is this only a warning light (message, guard, log or test) while the defect remains? Require `Not fixed yet: this helps find the cause` at the PR top, `Refs #N` rather than `Closes #N`, and keep the issue open.
6. Does every Story, PR-body and status claim match the evidence, including failures, skips and unproved criteria?

Write `<run folder>/review.md`. Its first line is exactly `Review: N must-fix` (replace N with the unresolved count), or `Review: no must-fix`. Follow with the six answers and concrete findings: location, evidence, consequence and required correction. Missing evidence is a limitation or finding, never a pass. Keep unresolved must-fixes visible when repair rounds are exhausted; never turn exhaustion into a clean verdict. The coordinating skill owns repair rounds and the existing PR gate.
