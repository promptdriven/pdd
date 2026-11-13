# Estimate nested check calls and guide refused target checks

As a developer who runs `pdd test`, I want nested prompt return turns counted in the call plan and refused target checks distinguished from running checks, so that I see a realistic call estimate and do not wait on a finished refusal.

## Acceptance criteria

1. For ready test "tests/install-pocket.json" with cap 18 whose step runs "prompts/pocket.prompt.md" (2 saved-data operations, calling "prompts/layout.prompt.md" once with 2 saved-data operations and "prompts/profile.prompt.md" once with 2 saved-data operations), the call plan estimates 11 AI calls with maximum 36, 2 Check requests, 0 lint model calls and external resources present.
2. For ready test "tests/play-game.json" with cap 80 whose step runs "prompts/game.prompt.md" (0 saved-data operations, calling "prompts/board.prompt.md" up to 30 times with 0 saved-data operations), the call plan estimates 61 AI calls with maximum 160 and no external resources.
3. When target test "tests/install-pocket.json" finishes as refused, target checks stay not run with "tests/install-pocket.json" unresolved and guidance "Inspect refused target checks: tests/install-pocket.json. Follow each refusal Fix or Next step, then run a fresh pdd test check."
4. When target test "tests/install-pocket.json" is still running, target checks stay not run with "tests/install-pocket.json" unresolved and guidance "Read the saved batch for unresolved target checks; do not resend uncertain work."

## Rules to check

- Each executable child prompt call adds max_calls times (the called prompt's estimate plus 1 caller return turn); a native-only target adds 0 calls and no external-resource presence. Forbidden: omitting the caller return turn after an executable child call, or charging a return turn for a native-only target.
- A refused target check never becomes passed or failed, and mixed or open unresolved target checks (missing, waiting, sent, running, partial, unknown or not run) keep the saved-batch wait guidance. Forbidden: telling the developer to run a fresh check while any unresolved target check is still running or unknown.

## Coverage boundary

```pdd-boundary
prompts/cli/runtime-check-plan.prompt.md
```

The Runtime scenario checks supplied prompt-interface summaries and reduced result rows only. Native tests establish repository interface reads, Git/source capture and text rendering.
