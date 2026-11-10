# Run setup only with a ready workflow agent through Runtime ports

I can gate `pdd setup` on workflow agent readiness, emit the readiness hint or refusal guidance to stderr, and invoke the caller's setup callback at most once.

```pdd-boundary
prompts/cli/workflow-setup.prompt.md
```

## Acceptance criteria

1. When a workflow agent is ready with an optional fallback hint, `setupWithWorkflowAgent` writes the hint to stderr, invokes `setup.setup` once with the selected agent, `cwd` and `env`, and returns its integer `exitCode`.
2. When no workflow agent is ready, `setupWithWorkflowAgent` writes the readiness owner's actionable message to stderr, does not call `setup.setup`, and returns `exitCode: 1`.
3. When the setup callback is unavailable (`hasSetup: false`), `setupWithWorkflowAgent` writes the missing-action recovery instruction to stderr without calling `readiness.checkWorkflowAgents` and returns `exitCode: 1`.
4. Passing an empty `cwd` fails with `invalid_setup_input` before any port call.
