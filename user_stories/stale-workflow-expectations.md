# Refuse stale workflow commands

As a workflow caller that read a run state, I want mutating workflow commands to verify the state I read before acting, so a late request cannot approve, change, cancel, or open a newer state.

## Acceptance criteria

1. `pdd workflow approve`, `changes`, `cancel`, and `open` accept the documented `--expect-gate ID` and `--expect-step STEP` options; calls without either option retain their existing command forms and behavior.
2. When the supplied expectation matches the run's current gate or step, each command proceeds with its existing behavior and effects.
3. When the supplied expectation does not match the current run state, the command refuses with the single documented stale-expectation exit code, identifies the current gate or step, and performs no run, approval, question, chat, file, branch, or publication change.
4. Supplying an expectation never causes a command to act against a later state after the run has advanced; the guard is evaluated from the saved state immediately before the command's existing effects.

## Rules to check

- The stale guard is shared by all four commands and is checked before any mutation or external effect.
- The stale-refusal exit code and refusal wording are one documented public contract. Their values remain open until the person approves them; the runtime case must use the approved values.
- The stable gate ID, whether both expectation options may be supplied, malformed/unknown expectation handling, and whether a step means only the current unfinished step remain open decisions from issue #2572. Do not infer these choices from implementation details.

## Open questions

Issue #2572 does not decide the stable value represented by gate `ID`, whether `--expect-gate` and `--expect-step` are mutually exclusive, how malformed or unknown values are classified, or the fixed stale-refusal exit code and exact wording. Resolve these with the person before implementation and update this Story and its runtime cases with the approved values.
