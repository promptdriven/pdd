# Review contracts, cases and results

Use the [canonical Prompting guide](../../../docs/prompting-guide.md), already read in full before Story authoring, as the authority for prompt-writing decisions.

## Review the intended change

Show the useful outcome, the owning prompt and Story changes, and independent expected cases before implementation when the person asks for that sequence. Explain relevant preserved behavior and unresolved choices. The person's actual decision applies to the revision they saw; do not fabricate approval or turn a suggested option into their answer.

After feedback, pair each point with the change made. Highlight the revised behavior and identify anything not addressed. Keep the conversation simple; no mandatory server review, account selector or special approval command is required by this kit.

## Report actual evidence

Distinguish source inspection, contract review, test expectations, code-test results and the person's manual observations. Tests cover declared cases, not every possible input. A passing code test does not establish that the prompt expresses the intended need. A written test that was not run is a draft, not a pass. For a local workflow run, verified PR publication must remain bound to the exact source checked; later work or report edits cannot reuse an older pass. Passing test exits do not certify a changed execution input: the runner also rechecks the exact handoff, file hashes, HEAD/worktree and starting ancestry after execution. Formal verification is unrun unless an actual checker supplied a result with its assumptions and scope.

For user-facing changes, a short Start / Do / Expect checklist can help the person assess an actually available app. Writing that checklist does not launch or prepare a PDD Try session. Manual feedback is an observation, not a generated test verdict.

## Prepare a PR

Review the diff, summarize the accepted behavior, list actual tests and note remaining limits. Keep publication separate from local preparation. Use the person's normal Git/GitHub tools within the requested authority. A requested local workflow run can create real PRs at its PR stages. Its merge stages observe GitHub and never merge. Inspect the actual revision, contract files and test argv before approving a runner stage; preserve its saved run identity and verified PR link. Do not invent a PR URL or report a merge from a prepared summary.
