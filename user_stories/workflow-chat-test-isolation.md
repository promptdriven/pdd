# Run native tests inside a workflow chat

As a person running tests in a workflow chat, I want the same test result as outside the chat, so that the agent's step finishes without waiting on my live session or on input I did not supply.

## Acceptance criteria

1. Focused native tests and `npm test` remove the caller's Herdr and agent session environment before test code runs; subprocesses do not inherit those sessions either.
2. Tests can still supply their own synthetic session values, unrelated environment values remain available, and the caller's environment stays unchanged.
3. Tests finish with the caller's input left open and no reply supplied. The product formal test also finishes successfully under a synthetic workflow-chat environment.

## Native verification boundary

The owning [test harness prompt](../prompts/test/test-home-isolation.prompt.md) has no interpreter operation. Verify these criteria through focused helper imports, the actual npm test script in a synthetic checkout, and the existing product formal test. Use synthetic session selectors, keep stdin open, bound child lifetimes, and verify environment isolation before any test body runs. These checks cover session leakage and termination in that environment; they do not establish which native operation waited in the historical 40-minute runs.

```pdd-boundary
prompts/test/test-home-isolation.prompt.md
```
