# Check a Story with local lint

As a developer working offline, I want local lint to check my selected Story and its prompts, so that I can find static errors before sending a check.

## Acceptance criteria

1. `pdd lint --local` on a selected Story with an invalid Runtime interface reports the problem and exits 4.
2. `pdd lint --local` on a selected Story with a check using an unknown target reports the problem and exits 4.
3. `pdd lint --local` on a selected Story with a result check in an expected error step reports the problem and exits 4.
4. `pdd lint --local` on a selected Story with a result path that cannot exist in its closed result schema reports the problem and exits 4.

## What must not change

- Local lint makes no network, sign-in or AI call and remains a partial result.
- A valid current draft and advisory warnings alone do not cause a refusal.

## Rules to check

- A result path is admissible if at least one schema branch permits it, and refused when none permits it. Forbidden: rejecting a possible path or accepting an impossible path.

## Runtime boundary

The [Runtime client](../prompts/cli/runtime-client.prompt.md) declares this real command boundary native-only: Git discovery, source reads and private state writes cannot be bound through its transport and clock ports. Native tests exercise the command and [preflight](../prompts/cli/runtime-preflight.prompt.md) against temporary repositories; no Runtime pass is claimed.
