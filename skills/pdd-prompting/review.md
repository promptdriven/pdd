# Review prompts, Stories and results

The rules for prompts are in `guide.md`. Use them for this review.

## Review a prompt and its cases

- Read the prompt and its Dependencies as a new reader. Read each required file.
- Trace one normal case and one important edge case to their results.
- Look for missing inputs, rules that conflict, unclear defaults or empty values, and text that describes the code instead of the behavior.
- Check each expected result against the Story and the prompt, not against the code.
- Keep each test step small. One step = one action, or a short run of actions (about 10 moves, rows or calls). Split a long replay into steps with the expected state after each part. The server stops a step after 10 minutes.
- If a rule is not decided, ask the person. Do not copy what the code returns.
- Write which Story criteria have test cases and which do not.

## Review with the person

- Show the useful result, the prompt and Story changes, and the expected cases.
- Name the behavior that stays the same and the open choices.
- After feedback, pair each point with the change that you made. Name each point that you did not change.
- The person's decision applies only to the version that they saw. Never invent an approval. A passing test is not an approval.

## Report the evidence

- Keep these apart: you read the source, you reviewed the contract, you wrote tests, you ran tests, the person tried it.
- A test that you wrote but did not run is a draft, not a pass.
- A passing test covers only its cases. It does not prove that the prompt says what the person needs.
- Give the exact commands and their real output. Name each check that you could not run.
- A Runtime PASS counts only for a Story that the PR changes against its base (`git diff origin/main...HEAD`): its Story file or test file changed, or its test reaches a changed prompt. A PASS of another Story proves nothing for this PR.
- A failed check is a FAIL, also inside a check with no verdict (RUNBOOK §11). When the checks did not all pass, open the report.
- For a visible change, give a short Start / Do / Expect list so the person can try it.

## Prepare a PR

- Read the full diff. Sum up the approved behavior, the tests that ran and the limits that remain.
- A config or metadata file (`package.json`, a lock file, CI settings) needs no prompt and no Story. Never ask for a new prompt for it. Ask for a test only when the change alters a result that users see.
- Never invent a PR link or say that a PR merged when it did not.
- For a full suite or a build, use the shared machine queue: run the full-suite command with `pdd workflow suite --command COMMAND`. Wait for its result. Never start a second copy at the same time.

## Behavioral tests

Derive expectations from accepted requirements before viewing outputs. Check observable behavior, state, effects and diagnostic meaning. For native tests call the public operation. Could a signature-only change or empty stub pass? If so, improve the behavior check. Require exact text only when the accepted interface does. If Runtime cannot express the meaning, report that coverage untested and use independent behavior review or native checks; do not invent a comparator or claim a semantic pass.
