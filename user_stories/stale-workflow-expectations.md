# Refuse stale workflow commands

As a workflow caller that read a run state, I want mutating workflow commands to verify the state I read before acting, so a late request cannot approve, change, cancel, or open a newer state.

## Acceptance criteria

1. `pdd workflow approve`, `changes`, `cancel`, and `open` accept the documented `--expect-gate ID` or `--expect-step STEP` option; calls without either option retain their existing command forms and behavior, and supplying both options is refused.
2. Gate expectations use the stable `area:kind` ID saved in `run.gate.id`; a matching gate or step expectation lets each command proceed with its existing behavior and effects.
3. A well-formed expectation that does not match the current run state refuses with exit code 2 and reason `stale_expectation`.
4. A malformed or unknown expectation, or both expectation options together, refuses with exit code 2 and reason `invalid_expectation`.
5. Every refusal writes exactly `pdd workflow: refused reason=<reason> current_gate=<gate-id-or-none> current_step=<step-or-none>\n` to stderr, writes nothing to stdout, and performs no run, approval, question, chat, file, branch, or publication change.
6. The guard reads saved state once immediately before command effects, so an expectation cannot act against a later state after the run advances.

## Rules to check

- The stale guard is shared by approve, changes, cancel, and open and runs before any mutation or external effect.
- A gate ID is the stable `area:kind` string and is stored in `run.gate.id`; the same value is used for expectations, status, refusal messages, and other reports.
- `--expect-gate` and `--expect-step` are mutually exclusive. Missing both preserves unconditional behavior.
- A gate expectation is valid only when it is a known current `area:kind` ID; a step expectation is valid only when it is a known workflow step. Unknown or malformed values are `invalid_expectation`.
- A valid expectation that differs from the saved current gate or step is `stale_expectation`.
- All stale or invalid refusals use exit code 2 and the exact stderr line in AC5; they do not save or perform external effects.

## Current state for examples

The runtime cases use `run.gate.id = stories:approve` and `run.step = prompt-story`.
