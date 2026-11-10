# Render workflow Story cards, fingerprints and full check passes through Runtime ports

I can render a run's Story card, compute Story and test decision fingerprints, diff saved vs current fingerprints, and verify full check passes through declared blob, compute and preflight ports.

```pdd-boundary
prompts/cli/workflow-story-card.prompt.md
```

## Acceptance criteria

1. `storyCard` renders the issue title, asked text, verdict, Story criteria, test cases table, changed prompts and `ask-code` next-step footer, and fails with `invalid_story_card_input` when `root` is empty.
2. `storyFingerprint` computes the Story SHA-256 and the canonical decision SHA-256 of test `{criteria, cases}`, and fails with `invalid_story_fingerprint_input` when `root` is empty.
3. `fingerprintChanges` reports criterion additions/removals and test case expected-value changes, and fails with `invalid_fingerprint_input` when a row path is empty.
4. `fullCheckPass` reconciles `batch.json` and `summary.json` against `preflight.findTests` and `preflight.captureSource`, returning `pass: true` when all discovered tests and changed prompts match a passing snapshot, and fails with `invalid_full_check_input` when `root` or `stateDir` is empty.
